// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {IERC1271} from "./interfaces/IERC1271.sol";

import {TwoStepOwnable} from "./deployer/TwoStepOwnable.sol";
import {MultiCallContext} from "./multicall/MultiCallContext.sol";

import {FastLogic} from "./utils/FastLogic.sol";
import {MerkleProofLib} from "./vendor/MerkleProofLib.sol";
import {Recover, PackedSignature} from "./utils/Recover.sol";
import {SignatureCheckerLib} from "./vendor/SignatureCheckerLib.sol";

contract CrossChainReceiverFactory is IERC1271, MultiCallContext, TwoStepOwnable {
    using FastLogic for bool;
    using Recover for bytes32;

    CrossChainReceiverFactory private immutable _cachedThis;
    bytes32 private immutable _proxyInitHash;
    uint256 private immutable _cachedChainId;
    bytes32 private immutable _cachedDomainSeparator;
    string public constant name = "ZeroExCrossChainReceiver";
    bytes32 private constant _DOMAIN_TYPEHASH = 0x8cad95687ba82c2ce50e74f7b754645e5117c3a5bec8151c0726d5857980a866;
    bytes32 private constant _NAMEHASH = 0x819c7f86c24229cd5fed5a41696eb0cd8b3f84cc632df73cfd985e8b100980e8;
    IERC20 private constant _NATIVE = IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE);
    address private constant _TOEHOLD = 0x4e59b44847b379578588920cA78FbF26c0B4956C;
    address private constant _WNATIVE_SETTER = 0x7f88741Cf6fb6b54533884C001c0F5eF6706b324;
    bytes32 private constant _WNATIVE_STORAGE_INITHASH = keccak256(
        abi.encodePacked(
            hex"3273",
            _WNATIVE_SETTER,
            hex"1815601c57fe5b7f36585f54601d575f555f5f37365f34f05f816017575ffd5b5260205ff35b30ff5f52595ff3"
        )
    );
    bytes32 private constant _WNATIVE_SALT = keccak256("Wrapped Native Token Address");
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
                                        abi.encodePacked(hex"ff", _TOEHOLD, _WNATIVE_SALT, _WNATIVE_STORAGE_INITHASH)
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
    IERC20 private immutable _WNATIVE;

    error DeploymentFailed();
    error ApproveFailed();

    constructor() {
        require((msg.sender == _TOEHOLD && uint160(address(this)) >> 104 == 0) || block.chainid == 31337);
        require(_DOMAIN_TYPEHASH == keccak256("EIP712Domain(string name,uint256 chainId,address verifyingContract)"));
        require(_NAMEHASH == keccak256(bytes(name)));

        IERC20 wnative;
        address wnativeStorage = _WNATIVE_STORAGE;
        assembly ("memory-safe") {
            mstore(0x00, 0x00)
            extcodecopy(wnativeStorage, 0x0c, sub(extcodesize(wnativeStorage), 0x14), 0x14)
            wnative := mload(0x00)
        }
        wnative.balanceOf(address(this)); // check that `_WNATIVE` is ERC20-ish
        _WNATIVE = wnative;

        _cachedThis = this;
        _proxyInitHash = keccak256(
            bytes.concat(
                hex"60265f8160095f39f35f5f365f5f37365f6c",
                bytes13(uint104(uint160(address(this)))),
                hex"5af43d5f5f3e6022573d5ffd5b3d5ff3"
            )
        );
        _cachedChainId = block.chainid;
        _cachedDomainSeparator = _computeDomainSeparator();
    }

    modifier onlyProxy() {
        require(this != _cachedThis);
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

    function DOMAIN_SEPARATOR() public view onlyProxy returns (bytes32) {
        return _computeDomainSeparator();
    }

    function _verifyRoot(bytes32 root, address originalOwner) internal view {
        bytes32 initHash = _proxyInitHash;
        CrossChainReceiverFactory factory = _cachedThis;
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            // derive creation salt
            mstore(0x14, originalOwner)
            mstore(0x00, root)
            let salt := keccak256(0x00, 0x34)

            // 0xff + factory + salt + hash(initCode)
            mstore(0x4d, initHash)
            mstore(0x2d, salt)
            mstore(0x0d, factory)
            mstore(0x00, 0xff00000000000000)
            let computedAddress := keccak256(0x18, 0x55)

            // verify that `salt` was used to deploy `address(this)`
            if shl(0x60, xor(address(), computedAddress)) {
                mstore(0x00, 0x1e092104) // selector for `PermissionDenied()`
                revert(0x1c, 0x04)
            }

            // restore clobbered memory
            mstore(0x60, 0x00)
            mstore(0x40, ptr)
        }
    }

    function isValidSignature(bytes32 hash, bytes calldata signature)
        external
        view
        override
        /* `_verifyRoot` hashes `_cachedThis`, making this function implicitly `onlyProxy` */
        returns (bytes4)
    {
        address owner;
        bytes32[] calldata proof;
        bytes calldata extraData;

        // This assembly block is equivalent to:
        //     hash = keccak256(abi.encode(hash, block.chainid));
        // except that it's cheaper and doesn't allocate memory. We make the assumption here that
        // `block.chainid` cannot alias a valid tree node or signing hash. Realistically,
        // `block.chainid` cannot exceed 2**53 - 1 or it would cause significant issues elsewhere in
        // the ecosystem. This also means that the sort order of the hash and the chainid is
        // backwards from what `MerkleProofLib` produces, again protecting us against extension
        // attacks.
        assembly ("memory-safe") {
            mstore(0x00, hash)
            mstore(0x20, chainid())
            hash := keccak256(0x00, 0x40)
        }

        // This assembly block is equivalent to:
        //     (owner, proof, extraData) = abi.decode(signature, (address, bytes32[], bytes));
        // except we omit all the range and overflow checking.
        assembly ("memory-safe") {
            owner := calldataload(signature.offset)
            if shr(0xa0, owner) { revert(0x00, 0x00) }
            proof.offset := add(signature.offset, calldataload(add(0x20, signature.offset)))
            proof.length := calldataload(proof.offset)
            proof.offset := add(0x20, proof.offset)
            extraData.offset := add(signature.offset, calldataload(add(0x40, signature.offset)))
            extraData.length := calldataload(extraData.offset)
            extraData.offset := add(0x20, extraData.offset)
        }

        if (extraData.length != 0) {
            _verifyRoot(MerkleProofLib.getRoot(proof, ""), owner);
            if (_erc1271IsValidSignature(hash, extraData, owner))
                return IERC1271.isValidSignature.selector;
            return 0xffffffff;
        }

        _verifyRoot(MerkleProofLib.getRoot(proof, hash), owner);
        return IERC1271.isValidSignature.selector;
    }

    function eip712Domain()
        public
        view
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

    function deploy(bytes32 root, address owner, bool setOwner) external noDelegateCall returns (address proxy) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            // derive the deployment salt from the owner and chainid
            mstore(0x14, owner)
            mstore(0x00, root)
            let salt := keccak256(0x00, 0x34)

            // create a minimal proxy targeting this contract
            mstore(0x1d, 0x5af43d5f5f3e6022573d5ffd5b3d5ff3)
            mstore(0x0d, address())
            mstore(0x00, 0x60265f8160095f39f35f5f365f5f37365f6c)
            proxy := create2(0x00, 0x0e, 0x2f, salt)
            if iszero(proxy) {
                mstore(0x00, 0x30116425) // selector for `DeploymentFailed()`.
                revert(0x1c, 0x04)
            }

            // restore clobbered memory
            mstore(0x40, ptr)

            // If `setOwner == true`, this gets the selector for `setPendingOwner(address)`,
            // otherwise you get the selector for `cleanup(address)`. In both cases, the selector is
            // appended with `owner`'s padding
            let selector := xor(0xfbacefce000000000000000000000000, mul(0x3f8c8622000000000000000000000000, setOwner))

            // set the pending owner, or `selfdestruct` to the owner
            mstore(0x14, owner)
            mstore(0x00, selector)
            if iszero(call(gas(), proxy, 0x00, 0x10, 0x24, 0x00, 0x00)) {
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
        }
    }

    function setPendingOwner(address owner) external onlyFactory {
        _setPendingOwner(owner);
    }

    function approvePermit2(IERC20 token, uint256 amount) external onlyProxy returns (bool) {
        if (token == _NATIVE) {
            token = _WNATIVE;
            assembly ("memory-safe") {
                if iszero(call(gas(), token, amount, 0x00, 0x00, 0x00, 0x00)) {
                    let ptr := mload(0x40)
                    returndatacopy(ptr, 0x00, returndatasize())
                    revert(ptr, returndatasize())
                }
            }
        }
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            mstore(0x00, 0x095ea7b3) // selector for `approve(address,uint256)`
            mstore(0x20, 0x000000000022D473030F116dDEE9F6B43aC78BA3) // Permit2
            mstore(0x40, amount)

            if iszero(call(gas(), token, 0x00, 0x1c, 0x44, 0x00, 0x20)) {
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if iszero(or(and(eq(mload(0x00), 0x01), lt(0x1f, returndatasize())), iszero(returndatasize()))) {
                mstore(0x00, 0x3e3f8f73) // selector for `ApproveFailed()`
                revert(0x1c, 0x04)
            }

            mstore(0x00, 0x01)
            return(0x00, 0x20)
        }
    }

    function call(address payable target, uint256 value, bytes calldata data)
        external
        onlyOwner
        returns (bytes memory)
    {
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            calldatacopy(ptr, data.offset, data.length)
            let success := call(gas(), target, value, ptr, data.length, 0x00, 0x00)

            returndatacopy(add(0x40, ptr), 0x00, returndatasize())

            if iszero(success) { revert(add(0x40, ptr), returndatasize()) }

            mstore(add(0x20, ptr), returndatasize())
            mstore(ptr, 0x20)
            return(ptr, add(0x40, returndatasize()))
        }
    }

    function cleanup(address payable beneficiary) external {
        if (msg.sender == address(_cachedThis)) {
            selfdestruct(beneficiary);
        }

        address owner_ = owner();
        if (_msgSender() != owner_) {
            if (owner_ != address(0)) {
                _permissionDenied();
            }
            address pendingOwner_ = pendingOwner();
            if ((pendingOwner_ == address(0)).or(beneficiary != pendingOwner_)) {
                _permissionDenied();
            }
        }
        selfdestruct(beneficiary);
    }

    //////////////////////////////////
    // ERC7739 modified from Solady //
    //////////////////////////////////

    /// @dev `keccak256("PersonalSign(bytes prefixed)")`.
    bytes32 internal constant _PERSONAL_SIGN_TYPEHASH =
        0x983e65e5148e570cd828ead231ee759a8d7958721a768f93bc4483ba005c32de;

    /// @dev Returns whether the `msg.sender` is considered safe, such
    /// that we don't need to use the nested EIP-712 workflow.
    /// Override to return true for more callers.
    /// See: https://mirror.xyz/curiousapple.eth/pFqAdW2LiJ-6S4sg_u1z08k4vK6BCJ33LcyXpnNb8yU
    function _erc1271CallerIsSafe() internal view virtual returns (bool) {
        // The canonical `MulticallerWithSigner` at 0x000000000000D9ECebf3C23529de49815Dac1c4c
        // is known to include the account in the hash to be signed.
        return msg.sender == 0x000000000000D9ECebf3C23529de49815Dac1c4c;
    }

    /// @dev [MODIFIED]Returns whether the `hash` and `signature` are valid.
    /// Override if you need non-ECDSA logic.
    function _erc1271IsValidSignatureNowCalldata(bytes32 hash, bytes calldata signature, address owner)
        internal
        view
        virtual
        returns (bool)
    {
        return SignatureCheckerLib.isValidSignatureNowCalldata(owner, hash, signature);
    }

    /// @dev Unwraps and returns the signature.
    function _erc1271UnwrapSignature(bytes calldata signature)
        internal
        view
        virtual
        returns (bytes calldata result)
    {
        result = signature;
        /// @solidity memory-safe-assembly
        assembly {
            // Unwraps the ERC6492 wrapper if it exists.
            // See: https://eips.ethereum.org/EIPS/eip-6492
            if eq(
                calldataload(add(result.offset, sub(result.length, 0x20))),
                mul(0x6492, div(not(shr(address(), address())), 0xffff)) // `0x6492...6492`.
            ) {
                let o := add(result.offset, calldataload(add(result.offset, 0x40)))
                result.length := calldataload(o)
                result.offset := add(o, 0x20)
            }
        }
    }

    /// @dev [MODIFIED] Returns whether the `signature` is valid for the `hash.
    function _erc1271IsValidSignature(bytes32 hash, bytes calldata signature, address owner)
        internal
        view
        virtual
        returns (bool)
    {
        return _erc1271IsValidSignatureViaSafeCaller(hash, signature, owner)
            || _erc1271IsValidSignatureViaNestedEIP712(hash, signature, owner)
            || _erc1271IsValidSignatureViaRPC(hash, signature, owner);
    }

    /// @dev Performs the signature validation without nested EIP-712 if the caller is
    /// a safe caller. A safe caller must include the address of this account in the hash.
    function _erc1271IsValidSignatureViaSafeCaller(bytes32 hash, bytes calldata signature, address owner)
        internal
        view
        virtual
        returns (bool result)
    {
        if (_erc1271CallerIsSafe()) result = _erc1271IsValidSignatureNowCalldata(hash, signature, owner);
    }

    /// @dev [MODIFIED]ERC1271 signature validation (Nested EIP-712 workflow).
    ///
    /// This uses ECDSA recovery by default (see: `_erc1271IsValidSignatureNowCalldata`).
    /// It also uses a nested EIP-712 approach to prevent signature replays when a single EOA
    /// owns multiple smart contract accounts,
    /// while still enabling wallet UIs (e.g. Metamask) to show the EIP-712 values.
    ///
    /// Crafted for phishing resistance, efficiency, flexibility.
    /// __________________________________________________________________________________________
    ///
    /// Glossary:
    ///
    /// - `APP_DOMAIN_SEPARATOR`: The domain separator of the `hash` passed in by the application.
    ///   Provided by the front end. Intended to be the domain separator of the contract
    ///   that will call `isValidSignature` on this account.
    ///
    /// - `ACCOUNT_DOMAIN_SEPARATOR`: The domain separator of this account.
    ///   See: `EIP712._domainSeparator()`.
    /// __________________________________________________________________________________________
    ///
    /// For the `TypedDataSign` workflow, the final hash will be:
    /// ```
    ///     keccak256(\x19\x01 ‖ APP_DOMAIN_SEPARATOR ‖
    ///         hashStruct(TypedDataSign({
    ///             contents: hashStruct(originalStruct),
    ///             name: keccak256(bytes(eip712Domain().name)),
    ///             version: keccak256(bytes(eip712Domain().version)),
    ///             chainId: eip712Domain().chainId,
    ///             verifyingContract: eip712Domain().verifyingContract,
    ///             salt: eip712Domain().salt
    ///         }))
    ///     )
    /// ```
    /// where `‖` denotes the concatenation operator for bytes.
    /// The order of the fields is important: `contents` comes before `name`.
    ///
    /// The signature will be `r ‖ s ‖ v ‖ APP_DOMAIN_SEPARATOR ‖
    ///     contents ‖ contentsDescription ‖ uint16(contentsDescription.length)`,
    /// where:
    /// - `contents` is the bytes32 struct hash of the original struct.
    /// - `contentsDescription` can be either:
    ///     a) `contentsType` (implicit mode)
    ///         where `contentsType` starts with `contentsName`.
    ///     b) `contentsType ‖ contentsName` (explicit mode)
    ///         where `contentsType` may not necessarily start with `contentsName`.
    ///
    /// The `APP_DOMAIN_SEPARATOR` and `contents` will be used to verify if `hash` is indeed correct.
    /// __________________________________________________________________________________________
    ///
    /// For the `PersonalSign` workflow, the final hash will be:
    /// ```
    ///     keccak256(\x19\x01 ‖ ACCOUNT_DOMAIN_SEPARATOR ‖
    ///         hashStruct(PersonalSign({
    ///             prefixed: keccak256(bytes(\x19Ethereum Signed Message:\n ‖
    ///                 base10(bytes(someString).length) ‖ someString))
    ///         }))
    ///     )
    /// ```
    /// where `‖` denotes the concatenation operator for bytes.
    ///
    /// The `PersonalSign` type hash will be `keccak256("PersonalSign(bytes prefixed)")`.
    /// The signature will be `r ‖ s ‖ v`.
    /// __________________________________________________________________________________________
    ///
    /// For demo and typescript code, see:
    /// - https://github.com/junomonster/nested-eip-712
    /// - https://github.com/frangio/eip712-wrapper-for-eip1271
    ///
    /// Their nomenclature may differ from ours, although the high-level idea is similar.
    ///
    /// Of course, if you have control over the codebase of the wallet client(s) too,
    /// you can choose a more minimalistic signature scheme like
    /// `keccak256(abi.encode(address(this), hash))` instead of all these acrobatics.
    /// All these are just for widespread out-of-the-box compatibility with other wallet clients.
    /// We want to create bazaars, not walled castles.
    /// And we'll use push the Turing Completeness of the EVM to the limits to do so.
    function _erc1271IsValidSignatureViaNestedEIP712(bytes32 hash, bytes calldata signature, address owner)
        internal
        view
        virtual
        returns (bool result)
    {
        uint256 t = uint256(uint160(address(this)));
        // Forces the compiler to pop the variables after the scope, avoiding stack-too-deep.
        if (t != uint256(0)) {
            (
                ,
                string memory name_,
                string memory version,
                uint256 chainId,
                address verifyingContract,
                bytes32 salt,
            ) = eip712Domain();
            /// @solidity memory-safe-assembly
            assembly {
                t := mload(0x40) // Grab the free memory pointer.
                // Skip 2 words for the `typedDataSignTypehash` and `contents` struct hash.
                mstore(add(t, 0x40), keccak256(add(name_, 0x20), mload(name_)))
                mstore(add(t, 0x60), keccak256(add(version, 0x20), mload(version)))
                mstore(add(t, 0x80), chainId)
                mstore(add(t, 0xa0), shr(96, shl(96, verifyingContract)))
                mstore(add(t, 0xc0), salt)
                mstore(0x40, add(t, 0xe0)) // Allocate the memory.
            }
        }
        /// @solidity memory-safe-assembly
        assembly {
            let m := mload(0x40) // Cache the free memory pointer.
            // `c` is `contentsDescription.length`, which is stored in the last 2 bytes of the signature.
            let c := shr(240, calldataload(add(signature.offset, sub(signature.length, 2))))
            for {} 1 {} {
                let l := add(0x42, c) // Total length of appended data (32 + 32 + c + 2).
                let o := add(signature.offset, sub(signature.length, l)) // Offset of appended data.
                mstore(0x00, 0x1901) // Store the "\x19\x01" prefix.
                calldatacopy(0x20, o, 0x40) // Copy the `APP_DOMAIN_SEPARATOR` and `contents` struct hash.
                // Use the `PersonalSign` workflow if the reconstructed hash doesn't match,
                // or if the appended data is invalid, i.e.
                // `appendedData.length > signature.length || contentsDescription.length == 0`.
                if or(xor(keccak256(0x1e, 0x42), hash), or(lt(signature.length, l), iszero(c))) {
                    t := 0 // Set `t` to 0, denoting that we need to `hash = _hashTypedData(hash)`.
                    mstore(t, _PERSONAL_SIGN_TYPEHASH)
                    mstore(0x20, hash) // Store the `prefixed`.
                    hash := keccak256(t, 0x40) // Compute the `PersonalSign` struct hash.
                    break
                }
                // Else, use the `TypedDataSign` workflow.
                // `TypedDataSign({ContentsName} contents,string name,...){ContentsType}`.
                mstore(m, "TypedDataSign(") // Store the start of `TypedDataSign`'s type encoding.
                let p := add(m, 0x0e) // Advance 14 bytes to skip "TypedDataSign(".
                calldatacopy(p, add(o, 0x40), c) // Copy `contentsName`, optimistically.
                mstore(add(p, c), 40) // Store a '(' after the end.
                if iszero(eq(byte(0, mload(sub(add(p, c), 1))), 41)) {
                    let e := 0 // Length of `contentsName` in explicit mode.
                    for { let q := sub(add(p, c), 1) } 1 {} {
                        e := add(e, 1) // Scan backwards until we encounter a ')'.
                        if iszero(gt(lt(e, c), eq(byte(0, mload(sub(q, e))), 41))) { break }
                    }
                    c := sub(c, e) // Truncate `contentsDescription` to `contentsType`.
                    calldatacopy(p, add(add(o, 0x40), c), e) // Copy `contentsName`.
                    mstore8(add(p, e), 40) // Store a '(' exactly right after the end.
                }
                // `d & 1 == 1` means that `contentsName` is invalid.
                let d := shr(byte(0, mload(p)), 0x7fffffe000000000000010000000000) // Starts with `[a-z(]`.
                // Advance `p` until we encounter '('.
                for {} iszero(eq(byte(0, mload(p)), 40)) { p := add(p, 1) } {
                    d := or(shr(byte(0, mload(p)), 0x120100000001), d) // Has a byte in ", )\x00".
                }
                mstore(p, " contents,string name,string") // Store the rest of the encoding.
                mstore(add(p, 0x1c), " version,uint256 chainId,address")
                mstore(add(p, 0x3c), " verifyingContract,bytes32 salt)")
                p := add(p, 0x5c)
                calldatacopy(p, add(o, 0x40), c) // Copy `contentsType`.
                // Fill in the missing fields of the `TypedDataSign`.
                calldatacopy(t, o, 0x40) // Copy the `contents` struct hash to `add(t, 0x20)`.
                mstore(t, keccak256(m, sub(add(p, c), m))) // Store `typedDataSignTypehash`.
                // The "\x19\x01" prefix is already at 0x00.
                // `APP_DOMAIN_SEPARATOR` is already at 0x20.
                mstore(0x40, keccak256(t, 0xe0)) // `hashStruct(typedDataSign)`.
                // Compute the final hash, corrupted if `contentsName` is invalid.
                hash := keccak256(0x1e, add(0x42, and(1, d)))
                signature.length := sub(signature.length, l) // Truncate the signature.
                break
            }
            mstore(0x40, m) // Restore the free memory pointer.
        }
        if (t == uint256(0)) hash = _hashTypedData(hash); // `PersonalSign` workflow.
        result = _erc1271IsValidSignatureNowCalldata(hash, signature, owner);
    }

    /// @dev Performs the signature validation without nested EIP-712 to allow for easy sign ins.
    /// This function must always return false or revert if called on-chain.
    function _erc1271IsValidSignatureViaRPC(bytes32 hash, bytes calldata signature, address owner)
        internal
        view
        virtual
        returns (bool result)
    {
        // Non-zero gasprice is a heuristic to check if a call is on-chain,
        // but we can't fully depend on it because it can be manipulated.
        // See: https://x.com/NoahCitron/status/1580359718341484544
        if (tx.gasprice == uint256(0)) {
            /// @solidity memory-safe-assembly
            assembly {
                mstore(gasprice(), gasprice())
                // See: https://gist.github.com/Vectorized/3c9b63524d57492b265454f62d895f71
                let b := 0x000000000000378eDCD5B5B0A24f5342d8C10485 // Basefee contract,
                pop(staticcall(0xffff, b, codesize(), gasprice(), gasprice(), 0x20))
                // If `gasprice < basefee`, the call cannot be on-chain, and we can skip the gas burn.
                if iszero(mload(gasprice())) {
                    let m := mload(0x40) // Cache the free memory pointer.
                    mstore(gasprice(), 0x1626ba7e) // `isValidSignature(bytes32,bytes)`.
                    mstore(0x20, b) // Recycle `b` to denote if we need to burn gas.
                    mstore(0x40, 0x40)
                    let gasToBurn := or(add(0xffff, gaslimit()), gaslimit())
                    // Burns gas computationally efficiently. Also, requires that `gas > gasToBurn`.
                    if or(eq(hash, b), lt(gas(), gasToBurn)) { invalid() }
                    // Make a call to this with `b`, efficiently burning the gas provided.
                    // No valid transaction can consume more than the gaslimit.
                    // See: https://ethereum.github.io/yellowpaper/paper.pdf
                    // Most RPCs perform calls with a gas budget greater than the gaslimit.
                    pop(staticcall(gasToBurn, address(), 0x1c, 0x64, gasprice(), gasprice()))
                    mstore(0x40, m) // Restore the free memory pointer.
                }
            }
            result = _erc1271IsValidSignatureNowCalldata(hash, signature, owner);
        }
    }

    /// @dev [MODIFIED] Returns the hash of the fully encoded EIP-712 message for this domain,
    /// given `structHash`, as defined in
    /// https://eips.ethereum.org/EIPS/eip-712#definition-of-hashstruct.
    ///
    /// The hash can be used together with {ECDSA-recover} to obtain the signer of a message:
    /// ```
    ///     bytes32 digest = _hashTypedData(keccak256(abi.encode(
    ///         keccak256("Mail(address to,string contents)"),
    ///         mailTo,
    ///         keccak256(bytes(mailContents))
    ///     )));
    ///     address signer = ECDSA.recover(digest, signature);
    /// ```
    function _hashTypedData(bytes32 structHash) internal view virtual returns (bytes32 digest) {
        // We will use `digest` to store the domain separator to save a bit of gas.
        digest = _computeDomainSeparator();
        /// @solidity memory-safe-assembly
        assembly {
            // Compute the digest.
            mstore(0x00, 0x1901000000000000) // Store "\x19\x01".
            mstore(0x1a, digest) // Store the domain separator.
            mstore(0x3a, structHash) // Store the struct hash.
            digest := keccak256(0x18, 0x42)
            // Restore the part of the free memory slot that was overwritten.
            mstore(0x3a, 0)
        }
    }
}
