// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {MockERC20} from "@solmate/test/utils/mocks/MockERC20.sol";
import {DeployPermit2} from "lib/permit2/test/utils/DeployPermit2.sol";

import {BaseSettler} from "src/chains/Base/TakerSubmitted.sol";
import {BaseSettlerMetaTxn} from "src/chains/Base/MetaTxn.sol";
import {BaseSettlerIntent} from "src/chains/Base/Intent.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {ISettlerTakerSubmitted} from "src/interfaces/ISettlerTakerSubmitted.sol";
import {ISettlerMetaTxn} from "src/interfaces/ISettlerMetaTxn.sol";
import {IAttestation} from "src/interfaces/IAttestation.sol";
import {IMsgSender} from "src/interfaces/IMsgSender.sol";
import {PERMIT2} from "src/core/Permit2Payment.sol";
import {
    SignatureExpired,
    InvalidSignature,
    ActionInvalid,
    ReentrantPayer,
    ConfusedDeputy
} from "src/core/SettlerErrors.sol";
import {IDodoV2} from "src/core/DodoV2.sol";
import {Cuid} from "src/utils/Cuid.sol";
import {AddressDerivation} from "src/utils/AddressDerivation.sol";
import {
    uniswapV3BaseFactory,
    uniswapV3InitHash,
    uniswapV3ForkId,
    IUniswapV3Callback
} from "src/core/univ3forks/UniswapV3.sol";
import {Permit2Signature} from "test/utils/Permit2Signature.sol";

contract AttestUnitTest is Permit2Signature, DeployPermit2 {
    uint256 private constant AUTHORITY_KEY = 0x123456;
    uint256 private constant TAKER_KEY = 0x654321;
    bytes12 private constant ZID = hex"0123456789abcdef01234567";
    string private constant APPID = "ch72gsb320000udocl363eofy";
    BaseSettler private settler;
    AttestationCallbackHelper private reader;
    MockERC20 private token;
    address private taker;
    uint128 private packedAppid;

    function setUp() public {
        deployPermit2();
        settler = new BaseSettler(bytes20(0));
        reader = new AttestationCallbackHelper();
        token = new MockERC20("Token", "T", 18);
        taker = vm.addr(TAKER_KEY);
        packedAppid = _pack(APPID);
    }

    function _pack(string memory cuid) private pure returns (uint128 packed) {
        bytes memory text = bytes(cuid);
        for (uint256 i = 1; i < text.length; ++i) {
            uint8 character = uint8(text[i]);
            packed = packed * 36 + (character <= 57 ? character - 48 : character - 87);
        }
    }

    function _metadata() private view returns (bytes32) {
        return bytes32(ZID) | bytes32(uint256(packedAppid));
    }

    function _digest(address target, address payer, uint256 deadline, bytes32 metadata, uint256 chainId)
        private
        pure
        returns (bytes32)
    {
        bytes32 domain = keccak256(
            abi.encode(
                keccak256("EIP712Domain(string name,uint256 chainId,address verifyingContract)"),
                keccak256("0xSettler"),
                chainId,
                target
            )
        );
        bytes32 contents = keccak256(
            abi.encode(
                keccak256("Attestation(address taker,uint256 deadline,bytes12 zid,string appid)"),
                payer,
                deadline,
                bytes12(metadata),
                keccak256(bytes(Cuid.decode(uint128(uint256(metadata)))))
            )
        );
        return keccak256(abi.encodePacked(hex"1901", domain, contents));
    }

    function _signed(address target, address payer, uint256 deadline, bytes32 metadata, uint256 key)
        private
        view
        returns (bytes memory)
    {
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(key, _digest(target, payer, deadline, metadata, block.chainid));
        return abi.encodeCall(ISettlerActions.ATTEST, (deadline, r, bytes32(uint256(s) | uint256(v - 27) << 255)));
    }

    function _read(address target, bool unavailable) private view returns (bytes memory) {
        bytes memory data =
            unavailable ? abi.encodeCall(reader.checkUnavailable, (target)) : abi.encodeCall(reader.record, (target));
        return abi.encodeCall(ISettlerActions.BASIC, (address(0), 0, address(reader), 0, data));
    }

    function _actions(address target, address payer, uint256 deadline, bytes32 metadata)
        private
        view
        returns (bytes[] memory actions)
    {
        actions = new bytes[](2);
        actions[0] = _signed(target, payer, deadline, metadata, AUTHORITY_KEY);
        actions[1] = _read(target, false);
    }

    function _execute(bytes[] memory actions, bytes32 metadata, address payer) private {
        vm.prank(payer);
        settler.execute(ISettlerBase.AllowedSlippage(payable(address(0)), IERC20(address(0)), 0), actions, metadata);
    }

    function test_Attest_RecoversAuthorityAndClearsAvailability() public {
        reader.checkUnavailable(address(settler));
        _execute(_actions(address(settler), taker, block.timestamp, _metadata()), _metadata(), taker);
        assertEq(reader.taker(), taker);
        assertEq(reader.zid(), ZID);
        assertEq(reader.appid(), APPID);
        assertEq(reader.authority(), vm.addr(AUTHORITY_KEY));
        reader.checkUnavailable(address(settler));
    }

    function test_Attest_NextExecutionCannotReadPreviousAttestation() public {
        _execute(_actions(address(settler), taker, block.timestamp, _metadata()), _metadata(), taker);
        bytes[] memory actions = new bytes[](1);
        actions[0] = _read(address(settler), true);
        _execute(actions, _metadata(), taker);
        _execute(actions, _metadata(), address(1234));
    }

    function test_Attest_BeforeActionRevertsAndAfterActionSucceeds() public {
        bytes[] memory actions = new bytes[](3);
        actions[0] = _read(address(settler), true);
        actions[1] = _signed(address(settler), taker, block.timestamp, _metadata(), AUTHORITY_KEY);
        actions[2] = _read(address(settler), false);
        _execute(actions, _metadata(), taker);
        assertEq(reader.authority(), vm.addr(AUTHORITY_KEY));
    }

    function test_Attest_ZeroPayerCannotSetAttestation() public {
        bytes[] memory actions = _actions(address(settler), address(0), block.timestamp, _metadata());
        vm.expectRevert(ConfusedDeputy.selector);
        _execute(actions, _metadata(), address(0));
        reader.checkUnavailable(address(settler));
    }

    function test_Attest_OverwritesAuthorityAndAllowsSignatureReuse() public {
        bytes[] memory actions = new bytes[](3);
        actions[0] = _signed(address(settler), taker, block.timestamp, _metadata(), AUTHORITY_KEY);
        actions[1] = _signed(address(settler), taker, block.timestamp, _metadata(), AUTHORITY_KEY + 1);
        actions[2] = _read(address(settler), false);
        _execute(actions, _metadata(), taker);
        assertEq(reader.authority(), vm.addr(AUTHORITY_KEY + 1));
        _execute(actions, _metadata(), taker);
        assertEq(reader.authority(), vm.addr(AUTHORITY_KEY + 1));
    }

    function test_Attest_ExpiredDeadlineReverts() public {
        vm.warp(100);
        bytes[] memory actions = _actions(address(settler), taker, 99, _metadata());
        vm.expectRevert(abi.encodeWithSelector(SignatureExpired.selector, 99));
        _execute(actions, _metadata(), taker);
        reader.checkUnavailable(address(settler));
    }

    function test_Attest_InvalidRecoveryReverts() public {
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(ISettlerActions.ATTEST, (block.timestamp, bytes32(0), bytes32(0)));
        vm.expectRevert(InvalidSignature.selector);
        _execute(actions, _metadata(), taker);
        reader.checkUnavailable(address(settler));
    }

    function test_Attest_TruncatedArgumentsRevert() public {
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodePacked(ISettlerActions.ATTEST.selector, bytes32(block.timestamp), bytes32(uint256(1)));
        vm.expectRevert(new bytes(0));
        _execute(actions, _metadata(), taker);
    }

    function test_Attest_UnusedMetadataBytesDoNotChangeAuthority() public {
        bytes[] memory actions = _actions(address(settler), taker, block.timestamp, _metadata());
        _execute(actions, _metadata() | bytes32(uint256(type(uint32).max) << 128), taker);
        assertEq(reader.authority(), vm.addr(AUTHORITY_KEY));
    }

    function test_Attest_ChangedSignedFieldsRecoverDifferentAuthorities() public {
        bytes[] memory actions = _actions(address(settler), taker, block.timestamp, _metadata());
        _execute(actions, _metadata() ^ bytes32(uint256(1) << 255), taker);
        assertNotEq(reader.authority(), vm.addr(AUTHORITY_KEY));
        _execute(actions, _metadata() ^ bytes32(uint256(1)), taker);
        assertNotEq(reader.authority(), vm.addr(AUTHORITY_KEY));
        _execute(actions, _metadata(), address(1234));
        assertNotEq(reader.authority(), vm.addr(AUTHORITY_KEY));
        vm.chainId(1);
        _execute(actions, _metadata(), taker);
        assertNotEq(reader.authority(), vm.addr(AUTHORITY_KEY));
    }

    function test_Attest_VerifyingContractIsSigned() public {
        bytes[] memory actions = _actions(address(1234), taker, block.timestamp, _metadata());
        actions[1] = _read(address(settler), false);
        _execute(actions, _metadata(), taker);
        assertNotEq(reader.authority(), vm.addr(AUTHORITY_KEY));
    }

    function test_Attest_DomainSeparatorFollowsChainIdChanges() public {
        uint256[3] memory chainIds = [uint256(8453), uint256(1), uint256(8453)];
        for (uint256 i; i < chainIds.length; ++i) {
            vm.chainId(chainIds[i]);
            _execute(_actions(address(settler), taker, block.timestamp, _metadata()), _metadata(), taker);
            assertEq(reader.authority(), vm.addr(AUTHORITY_KEY));
        }
    }

    function test_Attest_NonzeroMsgValueDoesNotAffectRecovery() public {
        bytes[] memory actions = _actions(address(settler), taker, block.timestamp, _metadata());
        vm.deal(taker, 1);
        vm.prank(taker);
        settler.execute{value: 1}(
            ISettlerBase.AllowedSlippage(payable(address(0)), IERC20(address(0)), 0), actions, _metadata()
        );
        assertEq(reader.authority(), vm.addr(AUTHORITY_KEY));
    }

    function test_Attest_EmptyRecoveryOutputCannotReusePreviousAuthority() public {
        bytes[] memory actions = _actions(address(settler), taker, block.timestamp, _metadata());
        actions[1] = abi.encodeCall(ISettlerActions.ATTEST, (block.timestamp, bytes32(0), bytes32(0)));
        vm.expectRevert(InvalidSignature.selector);
        _execute(actions, _metadata(), taker);
        reader.checkUnavailable(address(settler));
    }

    function test_Attest_DeadlineIsSigned() public {
        (uint8 v, bytes32 r, bytes32 s) =
            vm.sign(AUTHORITY_KEY, _digest(address(settler), taker, block.timestamp, _metadata(), block.chainid));
        bytes[] memory actions = new bytes[](2);
        actions[0] = abi.encodeCall(
            ISettlerActions.ATTEST, (block.timestamp + 1, r, bytes32(uint256(s) | uint256(v - 27) << 255))
        );
        actions[1] = _read(address(settler), false);
        _execute(actions, _metadata(), taker);
        assertNotEq(reader.authority(), vm.addr(AUTHORITY_KEY));
    }

    function test_Attest_ZeroMetadataIsAvailableAfterAttest() public {
        _execute(_actions(address(settler), taker, block.timestamp, bytes32(0)), bytes32(0), taker);
        assertEq(reader.zid(), bytes12(0));
        assertEq(reader.appid(), "c00000000000000000");
        assertEq(reader.authority(), vm.addr(AUTHORITY_KEY));
    }

    function test_Attest_RevertedExecutionDoesNotLeaveAnAttestation() public {
        bytes[] memory actions = _actions(address(settler), taker, block.timestamp, _metadata());
        actions[1] = abi.encodeCall(ISettlerActions.NATIVE_CHECK, (uint256(0), uint256(0)));
        vm.expectRevert(abi.encodeWithSelector(SignatureExpired.selector, 0));
        _execute(actions, _metadata(), taker);
        actions = new bytes[](1);
        actions[0] = _read(address(settler), true);
        _execute(actions, _metadata(), taker);
    }

    function test_Attest_MetaTxnCannotUseAttestAsAuthentication() public {
        address target = deployCode("MetaTxn.sol:BaseSettlerMetaTxn", abi.encode(bytes20(0)));
        bytes[] memory actions = _actions(target, taker, block.timestamp, _metadata());
        ISettlerBase.AllowedSlippage memory slippage;
        vm.expectPartialRevert(ActionInvalid.selector);
        ISettlerMetaTxn(target).executeMetaTxn(slippage, actions, _metadata(), taker, bytes(""));
        reader.checkUnavailable(target);
    }

    function test_Attest_ReentrancyLockAndMsgSenderRemainValid() public {
        bytes[] memory actions = _actions(address(settler), taker, block.timestamp, _metadata());
        actions[1] = abi.encodeCall(
            ISettlerActions.BASIC,
            (address(0), 0, address(reader), 0, abi.encodeCall(reader.checkReentrancy, (address(settler), taker)))
        );
        _execute(actions, _metadata(), taker);
        assertEq(reader.authority(), vm.addr(AUTHORITY_KEY));
    }

    function test_Attest_ReadableFromArmedPoolCallback() public {
        MockERC20 buyToken = new MockERC20("Buy", "B", 18);
        (IERC20 token0, IERC20 token1) = address(token) < address(buyToken)
            ? (IERC20(address(token)), IERC20(address(buyToken)))
            : (IERC20(address(buyToken)), IERC20(address(token)));
        address pool = AddressDerivation.deriveDeterministicContract(
            uniswapV3BaseFactory, keccak256(abi.encode(token0, token1, uint24(3000))), uniswapV3InitHash
        );
        vm.etch(pool, address(new AttestingPool(token0, token1)).code);
        token.mint(address(settler), 1 ether);
        buyToken.mint(pool, 1 ether);
        bytes memory path =
            abi.encodePacked(address(token), uniswapV3ForkId, uint24(3000), uint160(0), address(buyToken));
        bytes[] memory actions = new bytes[](2);
        actions[0] = _signed(address(settler), taker, block.timestamp, _metadata(), AUTHORITY_KEY);
        actions[1] = abi.encodeCall(ISettlerActions.UNISWAPV3, (taker, 1_000_000, path, 1 ether - 1 wei));
        _execute(actions, _metadata(), taker);
        AttestingPool attesting = AttestingPool(pool);
        assertEq(attesting.taker(), taker);
        assertEq(attesting.zid(), ZID);
        assertEq(attesting.appid(), APPID);
        assertEq(attesting.authority(), vm.addr(AUTHORITY_KEY));
        assertEq(token.balanceOf(pool), 1 ether - 1 wei);
        assertEq(buyToken.balanceOf(taker), 1 ether - 1 wei);
    }

    function testFuzz_Attest_PackedMetadataRoundTrips(uint128 appid, bytes12 zid, uint128 duration) public {
        bytes32 metadata = bytes32(zid) | bytes32(uint256(appid));
        uint256 authorityKey = uint256(appid) + 1;
        bytes[] memory actions = new bytes[](2);
        actions[0] = _signed(address(settler), taker, block.timestamp + duration, metadata, authorityKey);
        actions[1] = _read(address(settler), false);
        _execute(actions, metadata, taker);
        assertEq(reader.taker(), taker);
        assertEq(reader.zid(), zid);
        assertEq(_pack(reader.appid()), appid);
        assertEq(reader.authority(), vm.addr(authorityKey));
    }

    function test_Cuid_SpecificationExamplesAndBoundaries() public pure {
        assertEq(Cuid.decode(_pack("ch72gsb320000udocl363eofy")), "ch72gsb320000udocl363eofy");
        assertEq(Cuid.decode(_pack("cjld2cjxh0000qzrmn831i7rn")), "cjld2cjxh0000qzrmn831i7rn");
        assertEq(Cuid.decode(0), "c00000000000000000");
        assertEq(Cuid.decode(36 ** 16 - 1), "c0zzzzzzzzzzzzzzzz");
        assertEq(Cuid.decode(36 ** 16), "c10000000000000000");
        assertEq(Cuid.decode(36 ** 24 - 1), "czzzzzzzzzzzzzzzzzzzzzzzz");
        assertEq(Cuid.decode(36 ** 24), "c1000000000000000000000000");
        assertEq(_pack(Cuid.decode(type(uint128).max)), type(uint128).max);
        uint128 packed = _pack("ch72gsb320000udocl363eofy");
        // Internal calls may preserve high bits: packed |= type(uint256).max << 128.
        assembly ("memory-safe") {
            packed := or(shl(0x80, not(0x00)), packed)
        }
        assertEq(Cuid.decode(packed), "ch72gsb320000udocl363eofy");
    }

    function _referenceCuid(uint128 packed) private pure returns (string memory) {
        bytes memory alphabet = "0123456789abcdefghijklmnopqrstuvwxyz";
        uint256 length = 17;
        for (uint256 remaining = uint256(packed) / 36 ** 17; remaining != 0; remaining /= 36) {
            ++length;
        }
        bytes memory result = new bytes(length + 1);
        result[0] = "c";
        for (uint256 i = length; i != 0; --i) {
            result[i] = alphabet[packed % 36];
            packed /= 36;
        }
        return string(result);
    }

    function test_Cuid_AllDigitPositionsAndLengthBoundaries() public pure {
        for (uint256 place = 1; place <= type(uint128).max; place *= 36) {
            assertEq(Cuid.decode(uint128(place - 1)), _referenceCuid(uint128(place - 1)));
            for (uint256 digit = 1; digit < 36 && digit * place <= type(uint128).max; ++digit) {
                uint128 packed = uint128(digit * place);
                assertEq(Cuid.decode(packed), _referenceCuid(packed));
                assertEq(Cuid.decode(packed + 1), _referenceCuid(packed + 1));
            }
        }
    }

    function testFuzz_Cuid_ReferenceAndMemory(uint256 input) public pure {
        uint128 packed;
        uint256 beforePtr;
        // Dirty input bits and reused memory must not affect the string or its padding.
        // packed = uint128(input); memory[free:free + 96] = 0xff; the last word is a guard.
        assembly ("memory-safe") {
            packed := input
            beforePtr := mload(0x40)
            mstore(beforePtr, not(0x00))
            mstore(add(0x20, beforePtr), not(0x00))
            mstore(add(0x40, beforePtr), not(0x00))
        }
        string memory actual = Cuid.decode(packed);
        uint256 actualPtr;
        uint256 afterPtr;
        uint256 padding;
        uint256 guard;
        uint256 zeroSlot;
        // The attestation ABI requires the string at the allocation start and a zero-padded data word.
        // padding = uint256(bytes32(actual)) << (8 * bytes(actual).length).
        assembly ("memory-safe") {
            actualPtr := actual
            afterPtr := mload(0x40)
            padding := shl(shl(0x03, mload(actual)), mload(add(0x20, actual)))
            guard := mload(add(0x40, beforePtr))
            zeroSlot := mload(0x60)
        }
        assertEq(actualPtr, beforePtr);
        assertEq(afterPtr, beforePtr + 64);
        assertEq(padding, 0);
        assertEq(guard, type(uint256).max);
        assertEq(zeroSlot, 0);
        assertEq(actual, _referenceCuid(uint128(input)));
    }

    function decodeCuid(uint128 packed) external pure returns (string memory) {
        return Cuid.decode(packed);
    }

    function test_Cuid_Gas_Zero() public view {
        assertEq(this.decodeCuid(0), "c00000000000000000");
    }

    function test_Cuid_Gas_Appid() public view {
        assertEq(this.decodeCuid(packedAppid), APPID);
    }

    function test_Cuid_Gas_Maximum() public view {
        assertEq(this.decodeCuid(type(uint128).max), "cf5lxx1zz5pnorynqglhzmsp33");
    }

    function _select(bytes[][] memory candidates) private view returns (bytes memory) {
        return
            abi.encodeCall(
                ISettlerActions.SELECT, (500_000, address(token), new uint256[](candidates.length), candidates)
            );
    }

    function test_Attest_SelectReadsOuterAttestation() public {
        bytes[][] memory candidates = new bytes[][](1);
        candidates[0] = new bytes[](1);
        candidates[0][0] = _read(address(settler), false);
        bytes[] memory actions = new bytes[](2);
        actions[0] = _signed(address(settler), taker, block.timestamp, _metadata(), AUTHORITY_KEY);
        actions[1] = _select(candidates);
        _execute(actions, _metadata(), taker);
        assertEq(reader.authority(), vm.addr(AUTHORITY_KEY));
    }

    function test_Attest_SelectRetainsChainSpecificDispatch() public {
        address pool = makeAddr("dodo pool");
        bytes memory swap = abi.encodeCall(IDodoV2.sellBase, (address(reader)));
        vm.mockCall(pool, swap, abi.encode(uint256(0)));
        vm.expectCall(pool, swap);
        bytes[][] memory candidates = new bytes[][](1);
        candidates[0] = new bytes[](2);
        candidates[0][0] = abi.encodeCall(ISettlerActions.DODOV2, (address(reader), address(token), 0, pool, false, 0));
        candidates[0][1] = _read(address(settler), false);
        bytes[] memory actions = new bytes[](2);
        actions[0] = _signed(address(settler), taker, block.timestamp, _metadata(), AUTHORITY_KEY);
        actions[1] = _select(candidates);
        _execute(actions, _metadata(), taker);
        assertEq(reader.authority(), vm.addr(AUTHORITY_KEY));
    }

    function test_Attest_SelectCannotDispatchAttest() public {
        bytes[][] memory candidates = new bytes[][](1);
        candidates[0] = _actions(address(settler), taker, block.timestamp, _metadata());
        bytes[] memory actions = new bytes[](1);
        actions[0] = _select(candidates);
        vm.expectPartialRevert(ActionInvalid.selector);
        _execute(actions, _metadata(), taker);
        reader.checkUnavailable(address(settler));
    }

    function test_Attest_NestedSelectCannotDispatchAttest() public {
        bytes[][] memory candidates = new bytes[][](1);
        candidates[0] = _actions(address(settler), taker, block.timestamp, _metadata());
        bytes memory nested = _select(candidates);
        candidates[0] = new bytes[](1);
        candidates[0][0] = nested;
        bytes[] memory actions = new bytes[](1);
        actions[0] = _select(candidates);
        vm.expectPartialRevert(ActionInvalid.selector);
        _execute(actions, _metadata(), taker);
    }

    function test_Attest_SelectCanSkipAttestCandidate() public {
        bytes[][] memory candidates = new bytes[][](2);
        candidates[0] = _actions(address(settler), taker, block.timestamp, _metadata());
        candidates[1] = new bytes[](1);
        candidates[1][0] = _read(address(settler), true);
        bytes[] memory actions = new bytes[](1);
        actions[0] = _select(candidates);
        _execute(actions, _metadata(), taker);
    }

    function test_Attest_MetaTxn() public {
        address target = deployCode("MetaTxn.sol:BaseSettlerMetaTxn", abi.encode(bytes20(0)));
        _executeMetaTxn(target, false);
        assertEq(reader.taker(), taker);
        assertEq(reader.authority(), vm.addr(AUTHORITY_KEY));
        reader.checkUnavailable(target);
    }

    function test_Attest_Intent() public {
        address target = deployCode("Intent.sol:BaseSettlerIntent", abi.encode(bytes20(0)));
        _executeMetaTxn(target, true);
        assertEq(reader.taker(), taker);
        assertEq(reader.authority(), vm.addr(AUTHORITY_KEY));
        reader.checkUnavailable(target);
    }

    function _executeMetaTxn(address target, bool intent) private {
        if (intent) {
            bytes32 slot = bytes32(uint256(uint96(uint256(keccak256("SettlerIntentSolverList")) - 1)));
            vm.store(target, keccak256(abi.encode(address(this), slot)), bytes32(uint256(1)));
        }
        token.mint(taker, 1);
        vm.prank(taker);
        token.approve(address(PERMIT2), 1);
        ISignatureTransfer.PermitTransferFrom memory permit = defaultERC20PermitTransfer(address(token), 1, 0);
        bytes[] memory actions = new bytes[](3);
        actions[0] = abi.encodeCall(ISettlerActions.METATXN_TRANSFER_FROM, (target, permit));
        actions[1] = _signed(target, taker, block.timestamp, _metadata(), AUTHORITY_KEY);
        actions[2] = _read(target, false);
        ISettlerBase.AllowedSlippage memory slippage =
            ISettlerBase.AllowedSlippage(payable(taker), IERC20(address(token)), 1);
        bytes32 witness;
        bytes32 typehash;
        if (intent) {
            witness = keccak256(
                abi.encode(keccak256("Slippage(address recipient,address buyToken,uint256 minAmountOut)"), slippage)
            );
            typehash = keccak256(
                "PermitWitnessTransferFrom(TokenPermissions permitted,address spender,uint256 nonce,uint256 deadline,Slippage slippage)Slippage(address recipient,address buyToken,uint256 minAmountOut)TokenPermissions(address token,uint256 amount)"
            );
        } else {
            witness = keccak256(
                abi.encode(
                    keccak256(
                        "SlippageAndActions(address recipient,address buyToken,uint256 minAmountOut,bytes[] actions)"
                    ),
                    slippage,
                    keccak256(abi.encodePacked(keccak256(actions[0]), keccak256(actions[1]), keccak256(actions[2])))
                )
            );
            typehash = keccak256(
                "PermitWitnessTransferFrom(TokenPermissions permitted,address spender,uint256 nonce,uint256 deadline,SlippageAndActions slippageAndActions)SlippageAndActions(address recipient,address buyToken,uint256 minAmountOut,bytes[] actions)TokenPermissions(address token,uint256 amount)"
            );
        }
        bytes memory sig =
            getPermitWitnessTransferSignature(permit, target, TAKER_KEY, typehash, witness, PERMIT2.DOMAIN_SEPARATOR());
        ISettlerMetaTxn(target).executeMetaTxn(slippage, actions, _metadata(), taker, sig);
    }
}

contract AttestationCallbackHelper {
    address public taker;
    bytes12 public zid;
    string public appid;
    address public authority;

    function record(address target) public {
        (taker, zid, appid, authority) = IAttestation(target).attestation();
    }

    function checkUnavailable(address target) external view {
        try IAttestation(target).attestation() returns (address, bytes12, string memory, address) {
            revert("attestation must be unavailable");
        } catch (bytes memory reason) {
            require(reason.length == 0, "nonempty attestation revert");
        }
    }

    function checkReentrancy(address target, address expectedTaker) external {
        require(IMsgSender(target).msgSender() == expectedTaker);
        try ISettlerTakerSubmitted(target)
            .execute(
                ISettlerBase.AllowedSlippage(payable(address(0)), IERC20(address(0)), 0), new bytes[](0), bytes32(0)
            ) returns (
            bool
        ) {
            revert("reentrant execution succeeded");
        } catch (bytes memory reason) {
            require(keccak256(reason) == keccak256(abi.encodeWithSelector(ReentrantPayer.selector, expectedTaker)));
        }
        record(target);
    }
}

contract AttestingPool {
    IERC20 private immutable _TOKEN0;
    IERC20 private immutable _TOKEN1;
    address public taker;
    bytes12 public zid;
    string public appid;
    address public authority;

    constructor(IERC20 token0, IERC20 token1) {
        _TOKEN0 = token0;
        _TOKEN1 = token1;
    }

    function swap(address recipient, bool zeroForOne, int256 amountSpecified, uint160, bytes calldata data)
        external
        returns (int256 amount0, int256 amount1)
    {
        // Settler is waiting for this pool's swap callback. A query with a different selector must
        // leave that expectation in place.
        (taker, zid, appid, authority) = IAttestation(msg.sender).attestation();
        (amount0, amount1) = zeroForOne ? (amountSpecified, -amountSpecified) : (-amountSpecified, amountSpecified);
        IUniswapV3Callback(msg.sender).uniswapV3SwapCallback(amount0, amount1, data);
        (zeroForOne ? _TOKEN1 : _TOKEN0).transfer(recipient, uint256(amountSpecified));
    }
}
