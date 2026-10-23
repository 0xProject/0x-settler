// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {MockERC20} from "@solmate/test/utils/mocks/MockERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {DeployPermit2} from "lib/permit2/test/utils/DeployPermit2.sol";
import {HyperEvmSettler} from "src/chains/HyperEvm/TakerSubmitted.sol";
import {HyperEvmSettlerMetaTxn} from "src/chains/HyperEvm/MetaTxn.sol";
import {HyperEvmSettlerIntent} from "src/chains/HyperEvm/Intent.sol";
import {HyperEvmBridgeSettler} from "src/chains/HyperEvm/BridgeSettler.sol";
import {IBridgeSettlerActions} from "src/bridge/IBridgeSettlerActions.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {PERMIT2} from "src/core/Permit2Payment.sol";
import {ConfusedDeputy, HyperCoreSystemAddress} from "src/core/SettlerErrors.sol";
import {IUniV2Pair} from "src/core/UniswapV2.sol";
import {kittenSwapForkId} from "src/core/univ3forks/KittenSwap.sol";
import {Permit2Signature} from "../../utils/Permit2Signature.sol";
import {RejectionFallbackDummy} from "../Utils.sol";

contract HyperEvmTakerHarness is HyperEvmSettler {
    constructor() HyperEvmSettler(bytes20(0)) {}

    function checkRecipient(address sender, address recipient, IERC20 token) external view {
        _checkRecipient(sender, recipient, token);
    }

    function restrictedTarget(address target) external view returns (bool) {
        return _isRestrictedTarget(target);
    }

    function hasRecipientCheck() external pure returns (bool) {
        return _hasRecipientCheck();
    }

    function recipientCheckNeedsToken() external pure returns (bool) {
        return _recipientCheckNeedsToken();
    }
}

contract HyperEvmMetaTxnHarness is HyperEvmSettlerMetaTxn {
    constructor() HyperEvmSettlerMetaTxn(bytes20(0)) {}

    function checkRecipient(address sender, address recipient, IERC20 token) external view {
        _checkRecipient(sender, recipient, token);
    }

    function restrictedTarget(address target) external view returns (bool) {
        return _isRestrictedTarget(target);
    }

    function hasRecipientCheck() external pure returns (bool) {
        return _hasRecipientCheck();
    }

    function recipientCheckNeedsToken() external pure returns (bool) {
        return _recipientCheckNeedsToken();
    }
}

contract HyperEvmIntentHarness is HyperEvmSettlerIntent {
    constructor() HyperEvmSettlerIntent(bytes20(0)) {}

    function checkRecipient(address sender, address recipient, IERC20 token) external view {
        _checkRecipient(sender, recipient, token);
    }

    function restrictedTarget(address target) external view returns (bool) {
        return _isRestrictedTarget(target);
    }

    function hasRecipientCheck() external pure returns (bool) {
        return _hasRecipientCheck();
    }

    function recipientCheckNeedsToken() external pure returns (bool) {
        return _recipientCheckNeedsToken();
    }
}

contract HyperEvmBridgeHarness is HyperEvmBridgeSettler {
    constructor() HyperEvmBridgeSettler(bytes20(0)) {}

    function checkRecipient(address sender, address recipient, IERC20 token) external view {
        _checkRecipient(sender, recipient, token);
    }

    function restrictedTarget(address target) external view returns (bool) {
        return _isRestrictedTarget(target);
    }

    function hasRecipientCheck() external pure returns (bool) {
        return _hasRecipientCheck();
    }

    function recipientCheckNeedsToken() external pure returns (bool) {
        return _recipientCheckNeedsToken();
    }
}

contract HyperEvmSystemContractsUnitTest is Permit2Signature, DeployPermit2 {
    bytes32 private constant FULL_PERMIT2_WITNESS_TYPEHASH = keccak256(
        "PermitWitnessTransferFrom(TokenPermissions permitted,address spender,uint256 nonce,uint256 deadline,SlippageAndActions slippageAndActions)SlippageAndActions(address recipient,address buyToken,uint256 minAmountOut,bytes[] actions)TokenPermissions(address token,uint256 amount)"
    );
    bytes32 private constant SLIPPAGE_AND_ACTIONS_TYPEHASH =
        keccak256("SlippageAndActions(address recipient,address buyToken,uint256 minAmountOut,bytes[] actions)");

    address private constant CORE_WRITER = 0x3333333333333333333333333333333333333333;
    address payable private constant HYPE_SYSTEM_ADDRESS = payable(0x2222222222222222222222222222222222222222);
    // USDT0 has HyperCore token index 268 (0x10c).
    address payable private constant USDT0_SYSTEM_ADDRESS = payable(0x200000000000000000000000000000000000010C);
    IERC20 private constant ETH = IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE);

    uint256 private constant TAKER_PRIVATE_KEY = 0x1337;
    address private taker = vm.addr(TAKER_PRIVATE_KEY);

    HyperEvmSettler private settler;
    HyperEvmSettlerMetaTxn private metaTxn;
    HyperEvmTakerHarness private harness;
    MockERC20 private sellToken;
    MockERC20 private buyToken;
    address payable private recipient;
    address private pool;

    function setUp() public {
        deployPermit2();
        sellToken = new MockERC20("Sell Token", "SELL", 18);
        buyToken = new MockERC20("Buy Token", "BUY", 18);
        recipient = payable(makeAddr("recipient"));
        pool = address(new RejectionFallbackDummy());
        settler = HyperEvmSettler(payable(deployCode("TakerSubmitted.sol:HyperEvmSettler", abi.encode(bytes20(0)))));
        metaTxn =
            HyperEvmSettlerMetaTxn(payable(deployCode("MetaTxn.sol:HyperEvmSettlerMetaTxn", abi.encode(bytes20(0)))));
        harness = HyperEvmTakerHarness(payable(deployCode("HyperEvmSystemContracts.t.sol:HyperEvmTakerHarness")));
        sellToken.mint(address(settler), 1 ether);
        buyToken.mint(address(settler), 1 ether);
        sellToken.mint(taker, 1 ether);
        vm.prank(taker);
        sellToken.approve(address(PERMIT2), type(uint256).max);
    }

    function test_SystemContracts_Basic_CoreWriter_Reverts() public {
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(ISettlerActions.BASIC, (address(0), 0, CORE_WRITER, 0, _addApiWallet()));
        vm.expectRevert(ConfusedDeputy.selector);
        settler.execute(_noSlippage(), actions, bytes32(0));
    }

    function test_SystemContracts_Bridge_Basic_CoreWriter_Reverts() public {
        HyperEvmBridgeSettler bridge = HyperEvmBridgeSettler(
            payable(deployCode("BridgeSettler.sol:HyperEvmBridgeSettler", abi.encode(bytes20(0))))
        );
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(IBridgeSettlerActions.BASIC, (address(0), 0, CORE_WRITER, 0, _addApiWallet()));
        vm.expectRevert(ConfusedDeputy.selector);
        bridge.execute(actions, bytes32(0));
    }

    function test_SystemContracts_Basic_TransferToSystemAddress_NotChecked() public {
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(
            ISettlerActions.BASIC,
            (address(0), 0, address(buyToken), 0, abi.encodeCall(IERC20.transfer, (USDT0_SYSTEM_ADDRESS, 1 ether)))
        );
        settler.execute(_noSlippage(), actions, bytes32(0));
        assertEq(buyToken.balanceOf(USDT0_SYSTEM_ADDRESS), 1 ether);
    }

    function test_SystemContracts_FinalTransfer_TokenSystemAddress_Reverts() public {
        vm.expectRevert(abi.encodeWithSelector(HyperCoreSystemAddress.selector, USDT0_SYSTEM_ADDRESS));
        settler.execute(
            ISettlerBase.AllowedSlippage(USDT0_SYSTEM_ADDRESS, IERC20(address(buyToken)), 1), new bytes[](0), bytes32(0)
        );
        assertEq(buyToken.balanceOf(address(settler)), 1 ether);
        assertEq(buyToken.balanceOf(USDT0_SYSTEM_ADDRESS), 0);
    }

    function test_SystemContracts_FinalTransfer_HypeSystemAddress_Reverts() public {
        vm.deal(address(settler), 1 ether);
        vm.expectRevert(abi.encodeWithSelector(HyperCoreSystemAddress.selector, HYPE_SYSTEM_ADDRESS));
        settler.execute(ISettlerBase.AllowedSlippage(HYPE_SYSTEM_ADDRESS, ETH, 1), new bytes[](0), bytes32(0));
        assertEq(address(settler).balance, 1 ether);
    }

    function test_SystemContracts_FinalTransfer_Recipient_Succeeds() public {
        settler.execute(
            ISettlerBase.AllowedSlippage(recipient, IERC20(address(buyToken)), 1), new bytes[](0), bytes32(0)
        );
        assertEq(buyToken.balanceOf(recipient), 1 ether - 1);
        assertEq(buyToken.balanceOf(address(settler)), 1);
    }

    function test_SystemContracts_PositiveSlippage_SystemAddress_Reverts() public {
        _expectBlocked(
            abi.encodeCall(
                ISettlerActions.POSITIVE_SLIPPAGE, (USDT0_SYSTEM_ADDRESS, address(buyToken), 0, 1_000_000, 1_000_000)
            ),
            USDT0_SYSTEM_ADDRESS
        );
    }

    function test_SystemContracts_UniswapV2_PoolPayment_SystemAddress_Reverts() public {
        vm.mockCall(
            pool,
            abi.encodeCall(IUniV2Pair.getReserves, ()),
            abi.encode(uint112(100 ether), uint112(100 ether), uint32(0))
        );
        _expectBlocked(
            abi.encodeCall(
                ISettlerActions.UNISWAPV2, (USDT0_SYSTEM_ADDRESS, address(sellToken), 1_000_000, pool, uint24(1), 0)
            ),
            USDT0_SYSTEM_ADDRESS
        );
    }

    function test_SystemContracts_UniswapV3_PoolPayment_SystemAddress_Reverts() public {
        bytes memory path =
            abi.encodePacked(address(sellToken), kittenSwapForkId, uint24(500), uint160(0), address(buyToken));
        _expectBlocked(
            abi.encodeCall(ISettlerActions.UNISWAPV3, (USDT0_SYSTEM_ADDRESS, 1_000_000, path, 0)), USDT0_SYSTEM_ADDRESS
        );
    }

    function test_SystemContracts_Rfq_MakerPayment_SystemAddress_Reverts() public {
        _expectBlocked(
            abi.encodeCall(
                ISettlerActions.RFQ,
                (USDT0_SYSTEM_ADDRESS, _permit(address(buyToken)), makeAddr("maker"), "", address(sellToken), 1 ether)
            ),
            USDT0_SYSTEM_ADDRESS
        );
    }

    function test_SystemContracts_Bebop_MakerPayment_SystemAddress_Reverts() public {
        ISettlerActions.BebopOrder memory order;
        order.maker_token = address(buyToken);
        order.maker_address = makeAddr("maker");
        ISettlerActions.BebopMakerSignature memory signature;
        _expectBlocked(
            abi.encodeCall(ISettlerActions.BEBOP, (HYPE_SYSTEM_ADDRESS, address(sellToken), order, signature, 0)),
            HYPE_SYSTEM_ADDRESS
        );
    }

    function test_SystemContracts_TransferFrom_SystemAddress_CreditsTaker() public {
        ISignatureTransfer.PermitTransferFrom memory permit = _permit(address(sellToken));
        bytes memory sig = getPermitTransferSignature(permit, address(settler), TAKER_PRIVATE_KEY, _permit2Domain());
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(ISettlerActions.TRANSFER_FROM, (USDT0_SYSTEM_ADDRESS, permit, sig));
        vm.prank(taker);
        settler.execute(_noSlippage(), actions, bytes32(0));
        assertEq(sellToken.balanceOf(USDT0_SYSTEM_ADDRESS), 1 ether);
        assertEq(sellToken.balanceOf(taker), 0);
    }

    function test_SystemContracts_Bridge_TransferFrom_SystemAddress_CreditsTaker() public {
        HyperEvmBridgeSettler bridge = HyperEvmBridgeSettler(
            payable(deployCode("BridgeSettler.sol:HyperEvmBridgeSettler", abi.encode(bytes20(0))))
        );
        ISignatureTransfer.PermitTransferFrom memory permit = _permit(address(sellToken));
        bytes memory sig = getPermitTransferSignature(permit, address(bridge), TAKER_PRIVATE_KEY, _permit2Domain());
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(IBridgeSettlerActions.TRANSFER_FROM, (USDT0_SYSTEM_ADDRESS, permit, sig));
        vm.prank(taker);
        bridge.execute(actions, bytes32(0));
        assertEq(sellToken.balanceOf(USDT0_SYSTEM_ADDRESS), 1 ether);
    }

    function test_SystemContracts_MetaTxnTransferFrom_SystemAddress_CreditsSigner() public {
        ISignatureTransfer.PermitTransferFrom memory permit = _permit(address(sellToken));
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(ISettlerActions.METATXN_TRANSFER_FROM, (USDT0_SYSTEM_ADDRESS, permit));
        ISettlerBase.AllowedSlippage memory slippage = _noSlippage();
        metaTxn.executeMetaTxn(slippage, actions, bytes32(0), taker, _metaTxnSignature(permit, slippage, actions));
        assertEq(sellToken.balanceOf(USDT0_SYSTEM_ADDRESS), 1 ether);
        assertEq(sellToken.balanceOf(taker), 0);
    }

    function test_SystemContracts_MetaTxnFinalTransfer_SystemAddress_Reverts() public {
        buyToken.mint(address(metaTxn), 1 ether);
        ISignatureTransfer.PermitTransferFrom memory permit = _permit(address(sellToken));
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(ISettlerActions.METATXN_TRANSFER_FROM, (address(metaTxn), permit));
        ISettlerBase.AllowedSlippage memory slippage =
            ISettlerBase.AllowedSlippage(USDT0_SYSTEM_ADDRESS, IERC20(address(buyToken)), 1);
        bytes memory sig = _metaTxnSignature(permit, slippage, actions);
        vm.expectRevert(abi.encodeWithSelector(HyperCoreSystemAddress.selector, USDT0_SYSTEM_ADDRESS));
        metaTxn.executeMetaTxn(slippage, actions, bytes32(0), taker, sig);
        assertEq(buyToken.balanceOf(USDT0_SYSTEM_ADDRESS), 0);
        assertEq(sellToken.balanceOf(taker), 1 ether);
    }

    function test_SystemContracts_Flavors_RestrictCoreWriter() public {
        _assertFlavor(
            harness.restrictedTarget(CORE_WRITER),
            harness.restrictedTarget(recipient),
            harness.hasRecipientCheck(),
            harness.recipientCheckNeedsToken()
        );
        HyperEvmMetaTxnHarness metaTxnHarness =
            HyperEvmMetaTxnHarness(payable(deployCode("HyperEvmSystemContracts.t.sol:HyperEvmMetaTxnHarness")));
        _assertFlavor(
            metaTxnHarness.restrictedTarget(CORE_WRITER),
            metaTxnHarness.restrictedTarget(recipient),
            metaTxnHarness.hasRecipientCheck(),
            metaTxnHarness.recipientCheckNeedsToken()
        );
        HyperEvmIntentHarness intentHarness =
            HyperEvmIntentHarness(payable(deployCode("HyperEvmSystemContracts.t.sol:HyperEvmIntentHarness")));
        _assertFlavor(
            intentHarness.restrictedTarget(CORE_WRITER),
            intentHarness.restrictedTarget(recipient),
            intentHarness.hasRecipientCheck(),
            intentHarness.recipientCheckNeedsToken()
        );
        HyperEvmBridgeHarness bridgeHarness =
            HyperEvmBridgeHarness(payable(deployCode("HyperEvmSystemContracts.t.sol:HyperEvmBridgeHarness")));
        _assertFlavor(
            bridgeHarness.restrictedTarget(CORE_WRITER),
            bridgeHarness.restrictedTarget(recipient),
            bridgeHarness.hasRecipientCheck(),
            bridgeHarness.recipientCheckNeedsToken()
        );
    }

    function test_SystemContracts_Flavors_BlockSystemAddresses() public {
        HyperEvmMetaTxnHarness metaTxnHarness =
            HyperEvmMetaTxnHarness(payable(deployCode("HyperEvmSystemContracts.t.sol:HyperEvmMetaTxnHarness")));
        HyperEvmIntentHarness intentHarness =
            HyperEvmIntentHarness(payable(deployCode("HyperEvmSystemContracts.t.sol:HyperEvmIntentHarness")));
        HyperEvmBridgeHarness bridgeHarness =
            HyperEvmBridgeHarness(payable(deployCode("HyperEvmSystemContracts.t.sol:HyperEvmBridgeHarness")));
        vm.expectRevert(abi.encodeWithSelector(HyperCoreSystemAddress.selector, HYPE_SYSTEM_ADDRESS));
        metaTxnHarness.checkRecipient(address(metaTxnHarness), HYPE_SYSTEM_ADDRESS, ETH);
        vm.expectRevert(abi.encodeWithSelector(HyperCoreSystemAddress.selector, USDT0_SYSTEM_ADDRESS));
        intentHarness.checkRecipient(pool, USDT0_SYSTEM_ADDRESS, IERC20(address(buyToken)));
        vm.expectRevert(abi.encodeWithSelector(HyperCoreSystemAddress.selector, USDT0_SYSTEM_ADDRESS));
        bridgeHarness.checkRecipient(address(bridgeHarness), USDT0_SYSTEM_ADDRESS, IERC20(address(buyToken)));
    }

    function test_SystemContracts_NearMiss_Allowed() public view {
        // First byte 0x20 but a nonzero byte above the index: not a system address.
        harness.checkRecipient(address(harness), 0x2000000000000000000000010000000000000000, IERC20(address(buyToken)));
        harness.checkRecipient(address(harness), 0x2100000000000000000000000000000000000000, IERC20(address(buyToken)));
        harness.checkRecipient(address(harness), 0x2222222222222222222222222222222222222221, ETH);
    }

    function testFuzz_SystemContracts_TokenSystemAddress_Blocked(uint64 tokenIndex, address sender) public {
        // Outside `execute` the payer slot is empty, so any nonzero sender is "not the payer".
        vm.assume(sender != address(0));
        address systemAddress = address(uint160(0x2000000000000000000000000000000000000000) | uint160(tokenIndex));
        vm.expectRevert(abi.encodeWithSelector(HyperCoreSystemAddress.selector, systemAddress));
        harness.checkRecipient(sender, systemAddress, IERC20(address(buyToken)));
    }

    function testFuzz_SystemContracts_OtherRecipient_Allowed(address other, address sender) public view {
        vm.assume(other != HYPE_SYSTEM_ADDRESS);
        vm.assume(uint160(other) >> 64 != 0x200000000000000000000000);
        harness.checkRecipient(sender, other, IERC20(address(buyToken)));
    }

    function _assertFlavor(
        bool coreWriterRestricted,
        bool recipientRestricted,
        bool hasRecipientCheck,
        bool recipientCheckNeedsToken
    ) private pure {
        assertTrue(coreWriterRestricted);
        assertFalse(recipientRestricted);
        assertTrue(hasRecipientCheck);
        assertFalse(recipientCheckNeedsToken);
    }

    function _expectBlocked(bytes memory action, address blockedRecipient) private {
        bytes[] memory actions = new bytes[](1);
        actions[0] = action;
        vm.expectRevert(abi.encodeWithSelector(HyperCoreSystemAddress.selector, blockedRecipient));
        settler.execute(_noSlippage(), actions, bytes32(0));
        assertEq(sellToken.balanceOf(address(settler)), 1 ether);
        assertEq(buyToken.balanceOf(address(settler)), 1 ether);
    }

    function _metaTxnSignature(
        ISignatureTransfer.PermitTransferFrom memory permit,
        ISettlerBase.AllowedSlippage memory slippage,
        bytes[] memory actions
    ) private view returns (bytes memory) {
        bytes32[] memory actionHashes = new bytes32[](actions.length);
        for (uint256 i; i < actionHashes.length; i++) {
            actionHashes[i] = keccak256(actions[i]);
        }
        bytes32 witness = keccak256(
            abi.encode(
                SLIPPAGE_AND_ACTIONS_TYPEHASH,
                slippage.recipient,
                slippage.buyToken,
                slippage.minAmountOut,
                keccak256(abi.encodePacked(actionHashes))
            )
        );
        return getPermitWitnessTransferSignature(
            permit, address(metaTxn), TAKER_PRIVATE_KEY, FULL_PERMIT2_WITNESS_TYPEHASH, witness, _permit2Domain()
        );
    }

    function _permit2Domain() private view returns (bytes32) {
        return PERMIT2.DOMAIN_SEPARATOR();
    }

    function _addApiWallet() private pure returns (bytes memory) {
        return abi.encodeWithSignature(
            "sendRawAction(bytes)", abi.encodePacked(uint8(1), uint24(9), abi.encode(address(0xdead), ""))
        );
    }

    function _noSlippage() private pure returns (ISettlerBase.AllowedSlippage memory) {
        return ISettlerBase.AllowedSlippage(payable(address(0)), IERC20(address(0)), 0);
    }

    function _permit(address token) private view returns (ISignatureTransfer.PermitTransferFrom memory) {
        return defaultERC20PermitTransfer(token, 1 ether, 0);
    }
}
