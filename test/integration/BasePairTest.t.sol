// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "forge-std/Test.sol";
import {GasSnapshot} from "forge-gas-snapshot/GasSnapshot.sol";

import {IERC20} from "forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

import {Permit2Signature} from "../utils/Permit2Signature.sol";

import {SafeTransferLib} from "../../src/vendor/SafeTransferLib.sol";

abstract contract BasePairTest is Test, GasSnapshot, Permit2Signature {
    using SafeTransferLib for IERC20;

    uint256 internal constant FROM_PRIVATE_KEY = 0x1337;
    address internal FROM = vm.addr(FROM_PRIVATE_KEY);
    uint256 internal constant MAKER_PRIVATE_KEY = 0x0ff1c1a1;
    address internal MAKER = vm.addr(MAKER_PRIVATE_KEY);

    address internal constant BURN_ADDRESS = 0x2222222222222222222222222222222222222222;

    ISignatureTransfer internal constant PERMIT2 = ISignatureTransfer(0x000000000022D473030F116dDEE9F6B43aC78BA3);
    address internal constant ZERO_EX_ADDRESS = 0xDef1C0ded9bec7F1a1670819833240f027b25EfF;

    bytes32 internal immutable permit2Domain;

    constructor() {
        vm.createSelectFork(vm.envString("MAINNET_RPC_URL"), 18685612);
        permit2Domain = PERMIT2.DOMAIN_SEPARATOR();
    }

    function testName() internal virtual returns (string memory);
    function fromToken() internal virtual returns (IERC20);
    function toToken() internal virtual returns (IERC20);
    function amount() internal virtual returns (uint256);

    function setUp() public virtual {
        vm.createSelectFork(vm.envString("MAINNET_RPC_URL"), 18685612);
        vm.label(address(this), "FoundryTest");
        vm.label(FROM, "FROM");
        vm.label(MAKER, "MAKER");
        vm.label(BURN_ADDRESS, "BURN");

        // Initialize addresses with non-zero balances
        // https://github.com/0xProject/0x-settler#gas-comparisons
        if (address(fromToken()).code.length != 0) {
            deal(address(fromToken()), FROM, amount());
            deal(address(fromToken()), MAKER, 1);
            deal(address(fromToken()), BURN_ADDRESS, 1);
        }
        if (address(toToken()).code.length != 0) {
            deal(address(toToken()), MAKER, amount());
            deal(address(toToken()), BURN_ADDRESS, 1);
        }
    }

    function snapStartName(string memory name) internal {
        snapStart(string.concat(name, "_", testName()));
    }

    /// @dev Manually store a non-zero value as a nonce for Permit2
    /// note: we attempt to avoid touching storage by the usual means to side
    /// step gas metering
    function warmPermit2Nonce(address who) internal {
        // mapping(address => mapping(uint256 => uint256)) public nonceBitmap;
        //         msg.sender         wordPos    bitmap
        // as of writing, nonceBitmap begins at slot 0
        // keccak256(uint256(wordPos) . keccak256(uint256(msg.sender) . uint256(slot0)))
        // https://docs.soliditylang.org/en/v0.8.25/internals/layout_in_storage.html
        bytes32 slotId = keccak256(abi.encode(uint256(0), keccak256(abi.encode(who, uint256(0)))));
        bytes32 beforeValue = vm.load(address(PERMIT2), slotId);
        if (uint256(beforeValue) == 0) {
            vm.store(address(PERMIT2), slotId, bytes32(uint256(1)));
        }
    }

    /// @dev Manually store a non-zero value as a nonce for 0xV4 OTC Orders
    /// note: we attempt to avoid touching storage by the usual means to side
    /// step gas metering
    function warmZeroExOtcNonce(address who) internal {
        // mapping(address => mapping(uint64 => uint128)) txOriginNonces;
        //        tx.origin          bucket    min nonce
        // OtcOrders is 8th in LibStorage Enum
        bytes32 slotId = keccak256(abi.encode(uint256(0), keccak256(abi.encode(who, (uint256(8) + 1) << 128))));
        vm.store(address(ZERO_EX_ADDRESS), slotId, bytes32(uint256(1)));
    }

    modifier skipIf(bool condition) {
        if (!condition) {
            _;
        }
    }

    function safeApproveIfBelow(IERC20 token, address who, address spender, uint256 _amount) internal {
        // Can't use SafeTransferLib directly due to Foundry.prank not changing address(this)
        if (spender != address(0) && token.allowance(who, spender) < _amount) {
            vm.startPrank(who);
            SafeTransferLib.safeApprove(token, spender, type(uint256).max);
            vm.stopPrank();
        }
    }

    function balanceOf(IERC20 token, address account) internal view returns (uint256) {
        (bool success, bytes memory returnData) =
            address(this).staticcall(abi.encodeCall(this._balanceOf, (token, account)));
        assert(!success);
        assert(returnData.length == 32);
        return abi.decode(returnData, (uint256));
    }

    function _balanceOf(IERC20 token, address account) external view {
        uint256 result = token.balanceOf(account);
        assembly ("memory-safe") {
            mstore(0x00, result)
            revert(0x00, 0x20)
        }
    }
}
