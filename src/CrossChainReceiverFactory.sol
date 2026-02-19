// SPDX-License-Identifier: MIT
pragma solidity =0.8.34;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {IERC165} from "@forge-std/interfaces/IERC165.sol";
import {IERC1271} from "./interfaces/IERC1271.sol";
import {IERC5267} from "./interfaces/IERC5267.sol";
import {IOwnable} from "./interfaces/IOwnable.sol";

import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";

import {ICrossChainReceiverFactory} from "./interfaces/ICrossChainReceiverFactory.sol";
import {AbstractOwnable, OwnableImpl, TwoStepOwnable} from "./utils/TwoStepOwnable.sol";
import {IMultiCall, MultiCallContext, EIP150_MULTICALL_ADDRESS} from "./multicall/MultiCallContext.sol";

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
    bytes32 private immutable _proxyInitCode0 =
        bytes32(bytes20(0x60253d8160093d39F33d3d3D3D363D3D37363d6C)) | bytes32(uint256(uint160(address(this))) >> 8);
    bytes32 private immutable _proxyInitCode1 =
        bytes32(bytes1(uint8(uint160(address(this))))) | bytes32(uint256(0x5af43d3d93803e602357fd5bf3 << 144));
    bytes32 private immutable _proxyInitHash = keccak256(
        bytes.concat(
            hex"60253d8160093d39f33d3d3d3d363d3d37363d6c",
            bytes13(uint104(uint160(address(this)))),
            hex"5af43d3d93803e602357fd5bf3"
        )
    );

    string public constant override name = "ZeroExCrossChainReceiver";
    bytes32 private constant _NAMEHASH = 0x819c7f86c24229cd5fed5a41696eb0cd8b3f84cc632df73cfd985e8b100980e8;
    bytes32 private constant _DOMAIN_TYPEHASH = 0x8cad95687ba82c2ce50e74f7b754645e5117c3a5bec8151c0726d5857980a866;
    bytes32 private constant _SENTINEL_DOMAIN_SEPARATOR =
        0x645883bdca79cf2f0cd9e1ce41a5e705279b61c531a89508da475b856926949a;

    bytes32 private constant _MULTICALL_TYPEHASH = 0xd0290069becb7f8c7bc360deb286fb78314d4fb3e65d17004248ee046bd770a9;
    bytes32 private constant _CALL_TYPEHASH = 0xa8b3616b5b84550a806f58ebe7d19199754b9632d31e5e6d07e7faf21fe1cacc;

    address private constant _NATIVE_ADDRESS = 0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE;
    IERC20 private constant _NATIVE = IERC20(_NATIVE_ADDRESS);

    address private constant _ADDRESS_THIS_SENTINEL = 0x0000000000000061646472657373287468697329; // address(uint160(uint104(bytes13("address(this)"))))

    address private constant _TOEHOLD = 0x4e59b44847b379578588920cA78FbF26c0B4956C;
    address private constant _STORAGE_SETTER = 0x000000000000F01B1D1c8EEF6c6cF71a0b658Fbc;
    bytes32 private constant _STORAGE_INITHASH = keccak256(
        abi.encodePacked(
            hex"326d",
            uint112(uint160(_STORAGE_SETTER)),
            hex"1815601657fe5b7f60143603803560601c6d",
            uint112(uint160(_STORAGE_SETTER)),
            hex"14336c",
            uint40(uint104(uint160(EIP150_MULTICALL_ADDRESS)) >> 64),
            hex"3d527f",
            uint64(uint104(uint160(EIP150_MULTICALL_ADDRESS))),
            hex"1416602e57fe5b3d54604b57583d55803d3d373d34f03d8159526d6045573dfd5b5260203df35b30ff60901b5952604e3df3"
        )
    );

    function _getImmutableStorageAddress(bytes32 salt) private view returns (address) {
        return address(
            uint160(
                uint256(
                    keccak256(
                        abi.encodePacked(
                            hex"d694",
                            address(
                                uint160(
                                    uint256(
                                        keccak256(abi.encodePacked(hex"ff", _TOEHOLD, salt, _STORAGE_INITHASH))
                                    )
                                )
                            ),
                            hex"01"
                        )
                    )
                )
            )
        );
    }

    function _getImmutableAddress(bytes32 salt) private view returns (address) {
        return address(uint160(uint256(bytes32(_getImmutableStorageAddress(salt).code))));
    }

    bytes32 private constant _WNATIVE_STORAGE_SALT = keccak256("Wrapped Native Token Address");
    IWrappedNative private immutable _WNATIVE = IWrappedNative(payable(_getImmutableAddress(_WNATIVE_STORAGE_SALT)));
    bool private immutable _HAS_WNATIVE = true;
    bool private immutable _MISSING_WNATIVE = false;

    bytes32 private constant _MULTICALL_STORAGE_SALT = keccak256("ERC2771-forwarding MultiCall Address");
    IMultiCall private immutable _CHAIN_SPECIFIC_MULTICALL = IMultiCall(payable(_getImmutableAddress(_MULTICALL_STORAGE_SALT)));

    address private constant _PERMIT2_ADDRESS = 0x000000000022D473030F116dDEE9F6B43aC78BA3;
    ISignatureTransfer private constant _PERMIT2 = ISignatureTransfer(_PERMIT2_ADDRESS);

    error DeploymentFailed();
    error ApproveFailed();
    error InvalidNonce();
    error InvalidSigner();
    error SignatureExpired(uint256 deadline);

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
        require(_DOMAIN_TYPEHASH == keccak256("EIP712Domain(string name,uint256 chainId,address verifyingContract)"));
        require(
            _SENTINEL_DOMAIN_SEPARATOR
                == keccak256(
                    abi.encode(
                        keccak256("EIP712Domain(string name,address verifyingContract)"),
                        _NAMEHASH,
                        _ADDRESS_THIS_SENTINEL
                    )
                )
        );
        require(
            _MULTICALL_TYPEHASH
                == keccak256(
                    "MultiCall(Call[] calls,uint256 contextdepth,uint256 nonce,uint256 deadline)Call(address target,uint8 revertPolicy,uint256 value,bytes data)"
                )
        );
        require(_CALL_TYPEHASH == keccak256("Call(address target,uint8 revertPolicy,uint256 value,bytes data)"));

        {
            // Check that an OOG revert is bubbled, even when `revertPolicy == CONTINUE`
            address invalidTarget;
            assembly ("memory-safe") {
                mstore(0x00, 0x5b5860fe3d533df3)
                invalidTarget := create(0x00, 0x18, 0x08)
            }
            require(invalidTarget != address(0));

            IMultiCall.Call[] memory calls = new IMultiCall.Call[](1);
            calls[0].target = invalidTarget;
            calls[0].revertPolicy = IMultiCall.RevertPolicy.CONTINUE;
            try _MULTICALL().multicall{gas: 100_000}(calls, 0) {
                revert();
            } catch (bytes memory) { }

            // Check that a non-OOG revert is swallowed when `revertPolicy == CONTINUE`
            address revertTarget;
            assembly ("memory-safe") {
                mstore(0x00, 0x623d3dfd3d526003601df3)
                revertTarget := create(0x00, 0x15, 0x0b)
            }
            require(revertTarget != address(0));

            calls[0].target = revertTarget;
            IMultiCall.Result[] memory results = _MULTICALL().multicall{gas: 100_000}(calls, 0);
            require(results.length == 1);
            require(!results[0].success);
            require(results[0].data.length == 0);

            // Check that calling the identity precompile returns success and the expected echoed
            // data (including appended ERC2771 metadata)
            calls[0].target = address(4); // identity
            calls[0].revertPolicy = IMultiCall.RevertPolicy.REVERT;
            calls[0].data = "Hello, World!";
            results = _MULTICALL().multicall(calls, 1);
            require(results.length == 1);
            require(results[0].success);
            require(keccak256(results[0].data) == keccak256(bytes.concat("Hello, World!", bytes20(uint160(address(this))))));
        }

        if (address(_WNATIVE) == address(0)) {
            require(_getImmutableStorageAddress(_WNATIVE_STORAGE_SALT).codehash == 0xa4675c945174b9ec4e7010035cbc327beed918e1ea949cf630df20b201167a0c);
            // `_WNATIVE` is deliberately unset
            _HAS_WNATIVE = false;
            _MISSING_WNATIVE = true;
        } else {
            // do some behavioral checks on `_WNATIVE`

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

    function _requireOwner() internal view override(AbstractOwnable, OwnableImpl) onlyProxy {
        address msgSender = _msgSender();
        if (msgSender != address(this) && msgSender != super.owner()) {
            _permissionDenied();
        }
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
    // proxy. While this alone would ordinarily be sufficient to make any function that is
    // `onlyOwner` implicitly `onlyProxy`, including `renounceOwnership` and `transferOwnership`, we
    // have also explicitly made `_requireOwner()` `onlyProxy`.
    function owner() public view override(IOwnable, AbstractOwnable) onlyProxy returns (address) {
        return super.owner();
    }

    // Like `owner()`, function is overridden so that it is explicit that it is only meaningful on
    // the proxy. This also makes `acceptOwnership` and `rejectOwnership` implicitly `onlyProxy`.
    function pendingOwner() public view override onlyProxy returns (address) {
        return super.pendingOwner();
    }

    function _MULTICALL() internal view override returns (IMultiCall) {
        return _CHAIN_SPECIFIC_MULTICALL;
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
                return _verifyDeploymentRootHash(_getMerkleRoot(proof, _hashLeaf(hash)), originalOwner)
                    .ternary(IERC1271.isValidSignature.selector, bytes4(0xffffffff));
            }
        }

        // ERC7739 validation
        return _verifyERC7739NestedTypedSignature(hash, signature, super.owner())
            .ternary(IERC1271.isValidSignature.selector, bytes4(0xffffffff));
    }

    function _hashLeaf(bytes32 signingHash) private view returns (bytes32 leafHash) {
        assembly ("memory-safe") {
            // This assembly block is equivalent to:
            //     hash = keccak256(abi.encode(hash, block.chainid));
            // except that it's cheaper and doesn't allocate memory. We make the assumption here
            // that `block.chainid` cannot alias a valid tree node or signing hash. Realistically,
            // `block.chainid` cannot exceed 2**53 - 1 or it would cause significant issues
            // elsewhere in the ecosystem. This also means that the sort order of the hash and the
            // chainid is backwards from what `_getMerkleRoot` produces, again protecting us against
            // extension attacks.
            mstore(callvalue(), signingHash)
            mstore(0x20, chainid())
            leafHash := keccak256(callvalue(), 0x40)
        }
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
        setOwnerNotCleanup = setOwnerNotCleanup.or(_MISSING_WNATIVE);
        bytes32 proxyInitCode0 = _proxyInitCode0;
        bytes32 proxyInitCode1 = _proxyInitCode1;
        assembly ("memory-safe") {
            // derive the deployment salt from the owner
            mstore(0x14, initialOwner)
            mstore(callvalue(), root)
            let salt := keccak256(callvalue(), 0x34)

            // create a minimal proxy targeting this contract
            mstore(callvalue(), proxyInitCode0)
            mstore(0x20, proxyInitCode1)
            proxy := create2(callvalue(), callvalue(), 0x2e, salt)
            if iszero(proxy) {
                mstore(callvalue(), 0x30116425) // selector for `DeploymentFailed()`.
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
            mstore(callvalue(), selector)
            if iszero(call(gas(), proxy, callvalue(), 0x10, 0x24, codesize(), callvalue())) {
                let ptr := mload(0x40)
                returndatacopy(ptr, callvalue(), returndatasize())
                revert(ptr, returndatasize())
            }
        }
    }

    /// @inheritdoc ICrossChainReceiverFactory
    function setOwner(address owner_) external override onlyFactory {
        _setOwner(owner_);
    }

    /// @inheritdoc ICrossChainReceiverFactory
    function approvePermit2(IERC20 token, uint256 amount) external override onlyProxy returns (bool) {
        if (token == _NATIVE) {
            require(!_MISSING_WNATIVE);
            token = _WNATIVE;
            assembly ("memory-safe") {
                if iszero(call(gas(), token, amount, codesize(), callvalue(), codesize(), callvalue())) {
                    let ptr := mload(0x40)
                    returndatacopy(ptr, callvalue(), returndatasize())
                    revert(ptr, returndatasize())
                }
            }
        }
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            mstore(callvalue(), 0x095ea7b3) // selector for `approve(address,uint256)`
            mstore(0x20, _PERMIT2_ADDRESS)
            mstore(0x40, amount)

            if iszero(call(gas(), token, callvalue(), 0x1c, 0x44, callvalue(), 0x20)) {
                returndatacopy(ptr, callvalue(), returndatasize())
                revert(ptr, returndatasize())
            }
            // allow `approve` to either return `true` or empty to signal success
            if iszero(or(and(eq(mload(callvalue()), 0x01), lt(0x1f, returndatasize())), iszero(returndatasize()))) {
                mstore(callvalue(), 0x3e3f8f73) // selector for `ApproveFailed()`
                revert(0x1c, 0x04)
            }

            mstore(callvalue(), 0x01)
            return(callvalue(), 0x20)
        }
    }

    /// @inheritdoc ICrossChainReceiverFactory
    function getFromMulticall(IERC20 token, address payable recipient) external override noDelegateCall returns (bool) {
        IMultiCall MULTICALL = _MULTICALL();
        assembly ("memory-safe") {
            recipient := xor(
                recipient,
                mul(iszero(shl(0x60, xor(_ADDRESS_THIS_SENTINEL, recipient))), xor(caller(), recipient))
            )
            for {} true {} {
                if shl(0x60, xor(_NATIVE_ADDRESS, token)) {
                    mstore(callvalue(), 0x70a08231)
                    mstore(0x20, MULTICALL)
                    if iszero(staticcall(gas(), token, 0x1c, 0x24, callvalue(), 0x20)) {
                        let ptr_ := mload(0x40)
                        returndatacopy(ptr_, callvalue(), returndatasize())
                        revert(ptr_, returndatasize())
                    }
                    if gt(0x20, returndatasize()) { revert(codesize(), callvalue()) }

                    let amount := mload(callvalue())
                    if iszero(amount) { break }

                    let ptr := mload(0x40)

                    mstore(ptr, 0x669a7d5e)                                                        // `IMultiCall.multicall.selector`
                    mstore(add(0x20, ptr), 0x40)                                                   // calls.offset
                    mstore(add(0x40, ptr), callvalue())                                            // contextdepth (ignored because we set `revertPolicy = REVERT`)
                    mstore(add(0x60, ptr), 0x01)                                                   // calls.length
                    mstore(add(0x80, ptr), 0x20)                                                   // calls[0].offset
                    mstore(add(0xa0, ptr), and(0xffffffffffffffffffffffffffffffffffffffff, token)) // calls[0].target
                    mstore(add(0xc0, ptr), callvalue())                                            // calls[0].revertPolicy = RevertPolicy.REVERT
                    mstore(add(0xe0, ptr), callvalue())                                            // calls[0].value
                    mstore(add(0x100, ptr), 0x80)                                                  // calls[0].data.offset

                    mstore(add(0x164, ptr), amount)
                    mstore(add(0x144, ptr), recipient)
                    mstore(add(0x130, ptr), 0xa9059cbb000000000000000000000000) // `IERC20.transfer.selector` with `recipient`'s padding

                    mstore(add(0x120, ptr), 0x44)                                                  // calls[0].data.length

                    if iszero(
                        call(gas(), MULTICALL, callvalue(), add(0x1c, ptr), 0x168, codesize(), callvalue())
                    ) {
                        let ptr_ := mload(0x40)
                        returndatacopy(ptr_, callvalue(), returndatasize())
                        revert(ptr_, returndatasize())
                    }

                    break
                }

                {
                    let amount := balance(MULTICALL)
                    if iszero(amount) { break }

                    let ptr := mload(0x40)

                    mstore(ptr, 0x669a7d5e)                                                            // `IMultiCall.multicall.selector`
                    mstore(add(0x20, ptr), 0x40)                                                       // calls.offset
                    mstore(add(0x40, ptr), callvalue())                                                // contextdepth (ignored because we set `revertPolicy = REVERT`)
                    mstore(add(0x60, ptr), 0x01)                                                       // calls.length
                    mstore(add(0x80, ptr), 0x20)                                                       // calls[0].offset
                    mstore(add(0xa0, ptr), and(0xffffffffffffffffffffffffffffffffffffffff, recipient)) // calls[0].target
                    mstore(add(0xc0, ptr), callvalue())                                                // calls[0].revertPolicy = RevertPolicy.REVERT
                    mstore(add(0xe0, ptr), amount)                                                     // calls[0].value
                    mstore(add(0x100, ptr), 0x80)                                                      // calls[0].data.offset
                    mstore(add(0x120, ptr), callvalue())                                               // calls[0].data.length

                    if iszero(
                        call(gas(), MULTICALL, callvalue(), add(0x1c, ptr), 0x124, codesize(), callvalue())
                    ) {
                        let ptr_ := mload(0x40)
                        returndatacopy(ptr_, callvalue(), returndatasize())
                        revert(ptr_, returndatasize())
                    }

                    break
                }
            }

            mstore(callvalue(), 0x01)
            return(callvalue(), 0x20)
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
            let success := call(gas(), target, value, ptr, data.length, codesize(), callvalue())

            // prohibit sending data to EOAs; prohibit sending zero value to EOAs
            if lt(or(returndatasize(), mul(iszero(data.length), value)), success) {
                if iszero(extcodesize(target)) { revert(codesize(), callvalue()) }
            }

            let paddedLength := and(not(0x1f), add(0x1f, returndatasize()))
            mstore(add(add(0x20, ptr), paddedLength), callvalue())
            returndatacopy(add(0x40, ptr), callvalue(), returndatasize())

            if iszero(success) { revert(add(0x40, mload(0x40)), returndatasize()) }

            mstore(add(0x20, ptr), returndatasize())
            mstore(ptr, 0x20)
            return(ptr, add(0x40, paddedLength))
        }
    }

    /// @inheritdoc ICrossChainReceiverFactory
    function call(address payable target, IERC20 token, uint256 ppm, uint256 patchOffset, bytes calldata data)
        external
        payable
        override
        onlyOwner
        returns (bytes memory)
    {
        assembly ("memory-safe") {
            // empty data with offset == 0 is OK. otherwise, perform bounds checking
            if iszero(lt(add(0x1f, patchOffset), data.length)) {
                if or(shl(0x60, xor(_NATIVE_ADDRESS, token)), or(data.length, patchOffset)) {
                    mstore(0x00, 0x4e487b71) // selector for `Panic(uint256)`
                    mstore(0x20, 0x32) // code for array out-of-bounds
                    revert(0x1c, 0x24)
                }
            }

            let patchBytes
            let value
            for {} true {} {
                if shl(0x60, xor(_NATIVE_ADDRESS, token)) {
                    mstore(0x00, 0x70a08231) // `IERC20.balanceOf.selector`
                    mstore(0x20, address())
                    if iszero(staticcall(gas(), token, 0x1c, 0x24, 0x00, 0x20)) {
                        let ptr_ := mload(0x40)
                        returndatacopy(ptr_, 0x00, returndatasize())
                        revert(ptr_, returndatasize())
                    }
                    if gt(0x20, returndatasize()) { revert(codesize(), 0x00) }

                    let thisBalance := mload(0x00)
                    patchBytes := mul(ppm, thisBalance)
                    if iszero(or(iszero(ppm), eq(div(patchBytes, ppm), thisBalance))) {
                        mstore(0x00, 0x4e487b71) // selector for `Panic(uint256)`
                        mstore(0x20, 0x11) // code for arithmetic overflow
                        revert(0x1c, 0x24)
                    }

                    patchBytes := div(patchBytes, 1000000)
                    value := callvalue()

                    break
                }

                patchBytes := mul(ppm, selfbalance())
                if iszero(or(iszero(ppm), eq(div(patchBytes, ppm), selfbalance()))) {
                    mstore(0x00, 0x4e487b71) // selector for `Panic(uint256)`
                    mstore(0x20, 0x11) // code for arithmetic overflow
                    revert(0x1c, 0x24)
                }

                patchBytes := div(patchBytes, 1000000)
                value := patchBytes

                break
            }

            let ptr := mload(0x40)
            calldatacopy(ptr, data.offset, data.length)
            mstore(add(patchOffset, ptr), patchBytes)

            let success := call(gas(), target, value, ptr, data.length, codesize(), 0x00)

            // prohibit sending data to EOAs; prohibit sending zero value to EOAs
            if lt(or(returndatasize(), mul(iszero(data.length), value)), success) {
                if iszero(extcodesize(target)) { revert(0x00, 0x00) }
            }

            let paddedLength := and(not(0x1f), add(0x1f, returndatasize()))
            mstore(add(add(0x20, ptr), paddedLength), 0x00)
            returndatacopy(add(0x40, ptr), 0x00, returndatasize())

            if iszero(success) { revert(add(0x40, mload(0x40)), returndatasize()) }

            mstore(add(0x20, ptr), returndatasize())
            mstore(ptr, 0x20)
            return(ptr, add(0x40, paddedLength))
        }
    }

    function _useUnorderedNonce(uint256 nonce) private {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            let wordPos := shr(0x08, nonce)
            let bitPos := shl(and(0xff, nonce), 0x01)
            mstore(callvalue(), 0x4fe02b44) // `ISignatureTransfer.nonceBitmap.selector`
            mstore(0x20, address())
            mstore(0x40, wordPos)
            if iszero(staticcall(gas(), _PERMIT2_ADDRESS, 0x1c, 0x44, callvalue(), 0x20)) {
                returndatacopy(ptr, callvalue(), returndatasize())
                revert(ptr, returndatasize())
            }
            let canceledNonces := mload(callvalue())
            if and(canceledNonces, bitPos) {
                mstore(callvalue(), 0x756688fe) // `InvalidNonce.selector`
                revert(0x1c, 0x04)
            }
            mstore(callvalue(), 0x3ff9dcb1) // `ISignatureTransfer.invalidateUnorderedNonces.selector`
            mstore(returndatasize(), wordPos)
            mstore(0x40, bitPos)
            if iszero(call(gas(), _PERMIT2_ADDRESS, callvalue(), 0x1c, 0x44, codesize(), callvalue())) {
                returndatacopy(ptr, callvalue(), returndatasize())
                revert(ptr, returndatasize())
            }
            mstore(0x40, ptr)
        }
    }

    function _verifySimpleSignature(bytes32 signingHash, bytes calldata rvs, address owner_) private view {
        assembly ("memory-safe") {
            if xor(0x40, rvs.length) {
                mstore(callvalue(), 0x4e487b71) // selector for `Panic(uint256)`
                mstore(0x20, 0x32) // code for array out-of-bounds
                revert(0x1c, 0x24)
            }

            let ptr := mload(0x40)

            mstore(callvalue(), signingHash)
            let vs := calldataload(add(0x20, rvs.offset))
            mstore(0x20, add(0x1b, shr(0xff, vs))) // v
            mstore(0x40, calldataload(rvs.offset)) // r
            mstore(0x60, and(0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, vs)) // s

            let recovered := mload(staticcall(gas(), 0x01, callvalue(), 0x80, 0x01, 0x20))
            if shl(0x60, xor(owner_, recovered)) {
                mstore(callvalue(), 0x815e1d64) // `InvalidSigner.selector`
                revert(0x1c, 0x04)
            }
            mstore(0x40, ptr)
            mstore(0x60, callvalue())
        }
    }

    function _eip712SigningHash(bytes32 structHash) private view returns (bytes32 signingHash) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(callvalue(), _DOMAIN_TYPEHASH)
            mstore(0x20, _NAMEHASH)
            mstore(0x40, chainid())
            mstore(0x60, address())
            mstore(0x20, keccak256(0x00, 0x80))
            mstore(callvalue(), 0x1901)
            mstore(0x40, structHash)
            signingHash := keccak256(0x1e, 0x42)
            mstore(0x40, ptr)
            mstore(0x60, 0x00)
        }
    }

    // This function is provided for use with the Merkle proof flows inside `metaTx` where we can't
    // combine the EIP712 struct hash with the domain separator to derive the leaf of the tree
    // because the domain separator hashes over the address of the proxy, which is determined by the
    // root of the tree. This function breaks the hash cycle by substituting the sentinel for the
    // address of the proxy in the domain separator. For gas efficiency, we also omit the chainid
    // from the domain separator because the signing hash is first hashed with the chainid before
    // forming the Merkle leaf.
    function _nonEip712SigningHash(bytes32 structHash) private view returns (bytes32 signingHash) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(callvalue(), 0x1901)
            mstore(0x20, _SENTINEL_DOMAIN_SEPARATOR)
            mstore(0x40, structHash)
            signingHash := keccak256(0x1e, 0x42)
            mstore(0x40, ptr)
        }
    }

    // This function intentionally ignores any dirty bits that might be present in `calls`, assuming
    // that:
    //   1. The signer of the object wouldn't sign an invalid EIP712 serialization of the object
    //      containing dirty bits
    //   2. The object will be used later in a way that *does* check for dirty bits and causes a
    //      revert
    function _hashMultiCall(bytes calldata msgData, uint256 nonce, uint256 deadline)
        private
        view
        returns (bytes32 structHash, bytes memory data, uint256 totalValue)
    {
        assembly ("memory-safe") {
            // reencoding the `calls` argument or even just following the indirection pointer to the
            // encoded array of offsets and attempting to copy/forward only that portion of the
            // calldata is more complex and gas-expensive than just copying the whole thing
            // (including the signature) and forwarding it to `MultiCall`, so there will be a bunch
            // of extra garbage included with our call to `MultiCall.multicall` that is ignored when
            // that function decodes it.
            data := mload(0x40)
            let calls := add(0x20, data)

            let scratch
            {
                let argsLength := sub(msgData.length, 0x04)
                mstore(data, argsLength)
                calldatacopy(calls, add(0x04, msgData.offset), argsLength)
                scratch := add(calls, argsLength)
            }
            mstore(0x40, scratch)
            let lastWord := sub(scratch, 0x20)
            let contextdepth := mload(add(0x20, calls))

            // indirect `calls` so that it points to the beginning of the array of indirection
            // pointers to individual `IMultiCall.Call` structs
            let err
            {
                let offset := mload(calls)
                let oom := shr(0x40, offset)
                calls := add(offset, calls)
                err := or(lt(lastWord, calls), or(oom, err))
            }

            let callsLengthBytes
            {
                let callsLength := mload(calls)
                let oom := shr(0x3b, callsLength)
                callsLengthBytes := shl(0x05, callsLength)
                err := or(lt(lastWord, add(calls, callsLengthBytes)), or(oom, err))
            }
            calls := add(0x20, calls)

            for { let i } xor(i, callsLengthBytes) { i := add(0x20, i) } {
                let dst := add(i, scratch)
                let src := add(i, calls)

                // indirect `src` because it points to a dynamic type
                {
                    let offset := mload(src)
                    let oom := shr(0x40, offset)
                    src := add(calls, offset)
                    err := or(lt(lastWord, add(0x60, src)), or(oom, err))
                }

                // indirect `src.data` because it also points to a dynamic type
                let srcData
                let srcDataWord
                let srcDataWordValue
                {
                    srcDataWord := add(0x60, src)
                    srcDataWordValue := mload(srcDataWord)
                    let oom := shr(0x40, srcDataWordValue)
                    srcData := add(src, srcDataWordValue)
                    err := or(lt(lastWord, srcData), or(oom, err))
                }

                // decode the length of `src.data` and hash it
                {
                    let srcDataLength := mload(srcData)
                    let oom := shr(0x40, srcDataLength)
                    err := or(lt(lastWord, add(srcData, srcDataLength)), or(oom, err))
                    srcData := keccak256(add(0x20, srcData), srcDataLength)
                }

                // EIP712-hash the `Call` object into the `Call[]` array at `scratch[i]`
                let typeHashWord := sub(src, 0x20) // not technically memory safe
                let typeHashWordValue := mload(typeHashWord)
                mstore(typeHashWord, _CALL_TYPEHASH)
                mstore(srcDataWord, srcData)
                mstore(dst, keccak256(typeHashWord, 0xa0))
                mstore(typeHashWord, typeHashWordValue)
                mstore(srcDataWord, srcDataWordValue)

                // replace `src.target` with `address(this)` if it is `_ADDRESS_THIS_SENTINEL`
                let srcTarget := mload(src)
                mstore(src, xor(srcTarget, mul(eq(_ADDRESS_THIS_SENTINEL, srcTarget), xor(address(), srcTarget))))

                // if this addition overflows, then the call will fail inside `MultiCall` because we
                // won't have enough value to send. depending on the value of `revertPolicy` this
                // could be a GIGO error or cause the `multicall` to revert.
                totalValue := add(mload(add(0x40, src)), totalValue)
            }

            if err { revert(codesize(), callvalue()) }

            // hash the `Call[]` array
            let callsHash := keccak256(scratch, callsLengthBytes)

            // EIP712-encode the `MultiCall` object
            mstore(scratch, _MULTICALL_TYPEHASH)
            mstore(add(0x20, scratch), callsHash)
            mstore(add(0x40, scratch), contextdepth)
            mstore(add(0x60, scratch), nonce)
            mstore(add(0x80, scratch), deadline)

            // final hashing
            structHash := keccak256(scratch, 0xa0)
        }
    }

    /// @inheritdoc ICrossChainReceiverFactory
    function metaTx(
        IMultiCall.Call[] calldata /* calls */,
        uint256 /* contextdepth */,
        uint256 nonce,
        uint256 deadline,
        bytes calldata signature
    ) external override onlyProxy returns (IMultiCall.Result[] memory) {
        uint256 deadlineForHashing = deadline;
        {
            address relayer = address(uint160(deadline >> 96));
            if (relayer != address(0)) {
                if (relayer != _msgSender()) {
                    _permissionDenied();
                }
                deadline &= 0xffffffffffffffffffffffff;
            }
        }
        if (block.timestamp > deadline) {
            assembly ("memory-safe") {
                mstore(returndatasize(), 0xcd21db4f) // `SignatureExpired.selector`
                mstore(0x20, deadline)
                revert(0x1c, 0x24)
            }
        }

        // The upper 160 bits of the nonce encode the owner
        address owner_ = address(uint160(nonce >> 96));

        bytes memory data;
        uint256 value;
        if (owner_ != address(0)) {
            bytes32 structHash;
            (structHash, data, value) = _hashMultiCall(_msgData(), nonce, deadlineForHashing);
            bytes32 signingHash = _nonEip712SigningHash(structHash);

            bytes32[] calldata proof;
            assembly ("memory-safe") {
                // This assembly block simply ABIDecodes `proof` from `signature`. It omits range
                // and overflow checking.
                //     proof = abi.decode(signature, (bytes32[]));
                proof.offset := add(signature.offset, calldataload(signature.offset))
                proof.length := calldataload(proof.offset)
                proof.offset := add(0x20, proof.offset)
            }
            if (!_verifyDeploymentRootHash(_getMerkleRoot(proof, _hashLeaf(signingHash)), owner_)) {
                assembly ("memory-safe") {
                    mstore(callvalue(), 0x815e1d64) // `InvalidSigner.selector`
                    revert(0x1c, 0x04)
                }
            }
        } else {
            // `nonce`'s upper 160 bits will encode the *current* owner. This prevents "Nick's
            // Method" shenanigans as well as avoiding potential confusion when ownership is
            // transferred. Obviously if ownership is transferred *back* then confusion may occur,
            // but the `deadline` field should limit the blast radius of failures like that.
            owner_ = super.owner();
            nonce |= uint256(uint160(owner_)) << 96;

            bytes32 structHash;
            (structHash, data, value) = _hashMultiCall(_msgData(), nonce, deadlineForHashing);
            bytes32 signingHash = _eip712SigningHash(structHash);
            _verifySimpleSignature(signingHash, signature, owner_);
        }

        _useUnorderedNonce(nonce);

        unchecked {
            if (address(this).balance < value) {
                uint256 wrappedBalance;
                IWrappedNative wnative = _WNATIVE;
                bool hasWnative = _HAS_WNATIVE;
                assembly ("memory-safe") {
                    mstore(0x00, 0x70a08231) // `IERC20.balanceOf.selector`
                    mstore(0x20, address())

                    if iszero(staticcall(gas(), wnative, 0x1c, 0x24, callvalue(), 0x20)) {
                        // this should never happen
                        revert(codesize(), callvalue())
                    }

                    wrappedBalance := mul(hasWnative, mload(callvalue()))
                }

                uint256 toUnwrap = (address(this).balance + wrappedBalance < value)
                .ternary(wrappedBalance, value - address(this).balance);
                value = toUnwrap + address(this).balance;

                if (toUnwrap != 0) {
                    assembly ("memory-safe") {
                        mstore(callvalue(), 0x2e1a7d4d) // `IWrappedNative.withdraw.selector`
                        mstore(0x20, toUnwrap)

                        if iszero(call(gas(), wnative, callvalue(), 0x1c, 0x24, codesize(), callvalue())) {
                            // this should never happen
                            revert(codesize(), callvalue())
                        }
                    }
                }
            }
        }

        IMultiCall MULTICALL = _MULTICALL();
        assembly ("memory-safe") {
            let dataLength := mload(data)
            mstore(data, 0x669a7d5e) // `IMultiCall.multicall.selector`
            // we won't bother to restore `data.length` because this block never returns to Solidity

            let success := call(gas(), MULTICALL, value, add(0x1c, data), add(0x04, dataLength), codesize(), callvalue())

            // technically, this is not memory safe because there could be a hidden
            // compiler-allocated object at the end of `data` and the returndata from the `CALL`
            // could exceed `data.length`. in practice however, this is not a thing that happens, so
            // it's fine.
            returndatacopy(data, callvalue(), returndatasize())

            if iszero(success) { revert(data, returndatasize()) }

            let rds := returndatasize()

            let multicallBalance := balance(MULTICALL)
            if multicallBalance {
                // get any excess native value back out of `MultiCall`

                let ptr := add(add(0x20, returndatasize()), data)
                mstore(ptr, 0x669a7d5e) // `IMultiCall.multicall.selector`
                mstore(add(0x20, ptr), 0x40)             // calls.offset
                mstore(add(0x40, ptr), callvalue())      // contextdepth (ignored because we set `revertPolicy = REVERT`)
                mstore(add(0x60, ptr), 0x01)             // calls.length
                mstore(add(0x80, ptr), 0x20)             // calls[0].offset
                mstore(add(0xa0, ptr), address())        // calls[0].target
                mstore(add(0xc0, ptr), callvalue())      // calls[0].revertPolicy = RevertPolicy.REVERT
                mstore(add(0xe0, ptr), multicallBalance) // calls[0].value
                mstore(add(0x100, ptr), 0x80)            // calls[0].data.offset
                mstore(add(0x120, ptr), callvalue())     // calls[0].data.length

                if iszero(call(gas(), MULTICALL, callvalue(), add(0x1c, ptr), 0x124, codesize(), callvalue())) {
                    // this should never happen
                    revert(codesize(), callvalue())
                }
            }

            return(data, rds)
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
                        // this should never happen
                        revert(codesize(), callvalue())
                    }
                }
            }
        } else {
            _requireOwner();
        }
        selfdestruct(beneficiary);
    }

    /// Modified from Solady (https://github.com/Vectorized/solady/blob/b609a9c79ce541c2beca7a7d247665e7c93942a3/src/utils/MerkleProofLib.sol)
    /// Modified from Solmate (https://github.com/transmissions11/solmate/blob/main/src/utils/MerkleProofLib.sol)
    function _getMerkleRoot(bytes32[] calldata proof, bytes32 leaf) private view returns (bytes32 root) {
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
                    leaf := keccak256(callvalue(), 0x40) // Hash both slots of scratch space.

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
            mstore(callvalue(), root)
            let salt := keccak256(callvalue(), 0x34)

            // 0xff + factory + salt + hash(initCode)
            mstore(0x40, initHash)
            mstore(0x20, salt)
            mstore(callvalue(), factoryWithFF)
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
                mstore(0x60, callvalue())
                break
            }
            // Restore clobbered memory
            mstore(0x40, ptr)
        }
    }

    receive() external payable override onlyProxy {
        if ((msg.sender != address(_WNATIVE)).andNot(_MISSING_WNATIVE)) {
            IWrappedNative wnative = _WNATIVE;
            assembly ("memory-safe") {
                if iszero(
                    call(gas(), wnative, callvalue(), codesize(), returndatasize(), codesize(), returndatasize())
                ) {
                    // this should never happen
                    revert(codesize(), calldatasize())
                }
            }
        }
    }
}
