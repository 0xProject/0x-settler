// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {Test} from "forge-std/Test.sol";
import {GasSnapshot} from "forge-gas-snapshot/GasSnapshot.sol";

import {ERC20} from "solmate/src/tokens/ERC20.sol";
import {Permit2} from "permit2/src/Permit2.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

import {Permit2Signature} from "../utils/Permit2Signature.sol";

import {SafeTransferLib} from "../../src/utils/SafeTransferLib.sol";

abstract contract BasePairTest is Test, GasSnapshot, Permit2Signature {
    using SafeTransferLib for ERC20;

    uint256 internal constant FROM_PRIVATE_KEY = 0x1337;
    address FROM = vm.addr(FROM_PRIVATE_KEY);
    uint256 internal constant MAKER_PRIVATE_KEY = 0x0ff1c1a1;
    address MAKER = vm.addr(MAKER_PRIVATE_KEY);

    address internal constant BURN_ADDRESS = 0x2222222222222222222222222222222222222222;

    Permit2 internal constant PERMIT2 = Permit2(0x000000000022D473030F116dDEE9F6B43aC78BA3);
    address internal constant ZERO_EX_ADDRESS = 0xDef1C0ded9bec7F1a1670819833240f027b25EfF;

    function testName() internal virtual returns (string memory);
    function fromToken() internal virtual returns (ERC20);
    function toToken() internal virtual returns (ERC20);
    function amount() internal virtual returns (uint256);

    function setUp() public virtual {
        vm.createSelectFork(vm.envString("MAINNET_RPC_URL"));
        vm.label(address(this), "FoundryTest");
        vm.label(FROM, "FROM");

        deal(address(fromToken()), FROM, amount());
        deal(address(toToken()), MAKER, amount());
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
        // https://docs.soliditylang.org/en/v0.8.17/internals/layout_in_storage.html
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

    function safeApproveIfBelow(ERC20 token, address who, address spender, uint256 amount) internal {
        // Can't use SafeTransferLib directly due to Foundry.prank not changing address(this)
        if (spender != address(0) && token.allowance(who, spender) < amount) {
            vm.startPrank(who);
            SafeTransferLib.safeApprove(token, spender, type(uint256).max);
            vm.stopPrank();
        }
    }
}
