// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {IERC1271} from "./interfaces/IERC1271.sol";
import {IERC5267} from "./interfaces/IERC5267.sol";

import {TwoStepOwnable} from "./deployer/TwoStepOwnable.sol";
import {MultiCallContext, MULTICALL_ADDRESS} from "./multicall/MultiCallContext.sol";

import {FastLogic} from "./utils/FastLogic.sol";
import {MerkleProofLib} from "./vendor/MerkleProofLib.sol";

interface IWrappedNative is IERC20 {
    function deposit() external payable;
    function withdraw(uint256) external;

    event Deposit(address indexed, uint256);
    event Withdrawal(address indexed, uint256);

    receive() external payable;
}

contract CrossChainReceiverFactory is IERC1271, IERC5267, MultiCallContext, TwoStepOwnable {
    using FastLogic for bool;

    CrossChainReceiverFactory private immutable _cachedThis = this;
    bytes32 private immutable _proxyInitHash = keccak256(
        bytes.concat(
            hex"60265f8160095f39f35f5f365f5f37365f6c",
            bytes13(uint104(uint160(address(this)))),
            hex"5af43d5f5f3e6022573d5ffd5b3d5ff3"
        )
    );
    string public constant name = "ZeroExCrossChainReceiver";
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
            hex"5f527f",
            uint64(uint104(uint160(MULTICALL_ADDRESS))),
            hex"1416602e57fe5b5f54604b57585f55805f5f375f34f05f8159526d6045575ffd5b5260205ff35b30ff60901b5952604e5ff3"
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
            (bool success,) = payable(_WNATIVE).call{value: address(this).balance}("");
            require(success);
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

    // @inheritdoc IERC1271
    function isValidSignature(bytes32 hash, bytes calldata signature)
        external
        view
        override
        /* `_verifyDeploymentData` hashes `_cachedThis`, making this function implicitly `onlyProxy` */
        returns (bytes4)
    {
        // Merkle proof validation
        {
            address owner;
            bool validOwner;
            bytes32 leaf;
            bytes32[] calldata proof;

            assembly ("memory-safe") {
                // This assembly block is equivalent to:
                //     leaf = keccak256(abi.encode(hash, block.chainid));
                // except that it's cheaper and doesn't allocate memory. We make the assumption here that
                // `block.chainid` cannot alias a valid tree node or signing hash. Realistically,
                // `block.chainid` cannot exceed 2**53 - 1 or it would cause significant issues elsewhere in
                // the ecosystem. This also means that the sort order of the hash and the chainid is
                // backwards from what `MerkleProofLib` produces, again protecting us against extension
                // attacks.
                mstore(0x00, hash)
                mstore(0x20, chainid())
                leaf := keccak256(0x00, 0x40)

                // In merkle proof validation flow, signature is formed by (owner, proof)
                // Following assembly decodes the owner and checks it is a valid address
                owner := calldataload(signature.offset)
                validOwner := iszero(shr(0xa0, owner))
            }

            if (validOwner) {
                assembly ("memory-safe") {
                    // Following assembly decodes the proof without range and overflow checking
                    proof.offset := add(signature.offset, calldataload(add(0x20, signature.offset)))
                    proof.length := calldataload(proof.offset)
                    proof.offset := add(0x20, proof.offset)
                }
                if (_verifyDeploymentData(MerkleProofLib.getRoot(proof, leaf), owner)) {
                    return IERC1271.isValidSignature.selector;
                }
            }
        }

        // ERC7733 validation
        {
            // For automatic detection that the smart account supports the nested EIP-712 workflow,
            // See: https://eips.ethereum.org/EIPS/eip-7739.
            // If `hash` is `0x7739...7739`, returns `bytes4(0x77390001)`.
            // The returned number MAY be increased in future ERC7739 versions.
            unchecked {
                if (signature.length == uint256(0)) {
                    // Forces the compiler to optimize for smaller bytecode size.
                    if (uint256(hash) == ~signature.length / 0xffff * 0x7739) return 0x77390001;
                }
            }
            if (_verifyTypedDataSignature(hash, signature, owner())) {
                return IERC1271.isValidSignature.selector;
            }
            return 0xffffffff;
        }
    }

    // @inheritdoc IERC5267
    function eip712Domain()
        external
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

    function deploy(bytes32 root, address owner, bool setOwnerNotCleanup)
        external
        noDelegateCall
        returns (CrossChainReceiverFactory proxy)
    {
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

            // If `setOwnerNotCleanup == true`, this gets the selector for `setOwner(address)`,
            // otherwise you get the selector for `cleanup(address)`. In both cases, the selector is
            // appended with `owner`'s padding
            let selector :=
                xor(0xfbacefce000000000000000000000000, mul(0xe803affb000000000000000000000000, setOwnerNotCleanup))

            // set the owner, or `selfdestruct` to the owner
            mstore(0x14, owner)
            mstore(0x00, selector)
            if iszero(call(gas(), proxy, 0x00, 0x10, 0x24, 0x00, 0x00)) {
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
        }
    }

    function setOwner(address owner) external onlyFactory {
        _setOwner(owner);
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

    function _verifyDeploymentData(bytes32 root, address originalOwner) internal view returns (bool result) {
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

            // restore clobbered memory
            mstore(0x60, 0x00)
            mstore(0x40, ptr)

            // verify that `salt` was used to deploy `address(this)`
            result := iszero(shl(0x60, xor(address(), computedAddress)))
        }
    }

    // Modified from Solady (https://github.com/Vectorized/solady/blob/c4d32c3e6e89da0321fda127ff024eecd5b57bc6/src/accounts/ERC1271.sol#L120-L287) under the MIT license
    function _verifyTypedDataSignature(bytes32 hash, bytes calldata signature, address owner)
        internal
        view
        virtual
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
            mstore(0x00, 0x1901) // Store the "\x19\x01" prefix.
            calldatacopy(0x20, o, 0x40) // Copy the `APP_DOMAIN_SEPARATOR` and `contents` struct hash.
            // Dismiss the signature if:
            // 1. the reconstructed hash doesn't match,
            // 2. the appended data is invalid, i.e.
            //    (`appendedData.length > signature.length || contentsDescription.length == 0`.)
            // 3. the signature is not 64 bytes long
            for {} 1 {} {
                if or(xor(keccak256(0x1e, 0x42), hash), or(xor(add(0x40, l), signature.length), iszero(c))) {
                    break
                }
                    // Generate the `TypedDataSign` struct.
                    // `TypedDataSign({ContentsName} contents,string name,...){ContentsType}`.
                    // and check it was signed by the owner
                    let m := add(0xa0, ptr)
                    mstore(m, "TypedDataSign(") // Store the start of `TypedDataSign`'s type encoding.
                    let p := add(0x0e, m) // Advance 14 bytes to skip "TypedDataSign(".
                    calldatacopy(p, add(0x40, o), c) // Copy `contentsName`, optimistically.
                    mstore(add(p, c), 0x28) // Store a '(' after the end.
                    if iszero(eq(byte(0x00, mload(sub(add(p, c), 0x01))), 0x29)) {
                        let e := 0x00 // Length of `contentsName` in explicit mode.
                        for { let q := sub(add(p, c), 0x01) } 1 {} {
                            e := add(e, 0x01) // Scan backwards until we encounter a ')'.
                            if iszero(gt(lt(e, c), eq(byte(0x00, mload(sub(q, e))), 0x29))) { break }
                        }
                        c := sub(c, e) // Truncate `contentsDescription` to `contentsType`.
                        calldatacopy(p, add(add(0x40, o), c), e) // Copy `contentsName`.
                        mstore8(add(p, e), 0x28) // Store a '(' exactly right after the end.
                    }
                    // `d & 1 == 1` means that `contentsName` is invalid.
                    let d := shr(byte(0x00, mload(p)), 0x7fffffe000000000000010000000000) // Starts with `[a-z(]`.
                    // Advance `p` until we encounter '('.
                    for {} xor(0x28, shr(0xf8, mload(p))) { p := add(0x01, p) } {
                        d := or(shr(byte(0x00, mload(p)), 0x120100000001), d) // Has a byte in ", )\x00".
                    }
                    mstore(p, " contents,string name,uint256 ch") // Store the rest of the encoding.
                    mstore(add(0x20, p), "ainId,address verifyingContract)")
                    p := add(0x40, p)
                    calldatacopy(p, add(0x40, o), c) // Copy `contentsType`.
                    // Fill in the missing fields of the `TypedDataSign`.
                    calldatacopy(ptr, o, 0x40) // Copy the `contents` struct hash to `add(ptr, 0x20)`.
                    mstore(ptr, keccak256(m, sub(add(p, c), m))) // Store `typedDataSignTypehash`.
                    // The "\x19\x01" prefix is already at 0x00.
                    // `APP_DOMAIN_SEPARATOR` is already at 0x20.
                    mstore(0x40, keccak256(ptr, 0xa0)) // `hashStruct(typedDataSign)`.
                    // Compute the final hash, corrupted if `contentsName` is invalid.
                    hash := keccak256(0x1e, add(0x42, and(0x01, d)))

                    let vs := calldataload(add(0x20, signature.offset))

                    mstore(0x00, hash)
                    mstore(0x20, add(0x1b, shr(0xff, vs))) // `v`.
                    mstore(0x40, calldataload(signature.offset)) // `r`.
                    mstore(0x60, and(0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, vs)) // `s`.
                    let recovered := mload(staticcall(gas(), 0x01, 0x00, 0x80, 0x01, 0x20))
                    result := gt(returndatasize(), shl(0x60, xor(owner, recovered)))

                    // Restore clobbered memory
                    mstore(0x60, 0x00)
            }
            mstore(0x40, ptr)
        }
    }

    receive() external payable onlyProxy {}
}
