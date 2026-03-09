// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";

import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {Settler} from "src/Settler.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {IBebopSettlement} from "src/core/Bebop.sol";
import {ALLOWANCE_HOLDER} from "src/allowanceholder/IAllowanceHolder.sol";

import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";

abstract contract BebopPairTest is SettlerBasePairTest {
    IBebopSettlement internal constant BEBOP = IBebopSettlement(0xbbbbbBB520d69a9775E85b458C58c648259FAD5F);

    // EIP-712 domain separator for Bebop on mainnet:
    // keccak256(abi.encode(
    //     keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"),
    //     keccak256("BebopSettlement"),
    //     keccak256("2"),
    //     1,
    //     0xbbbbbBB520d69a9775E85b458C58c648259FAD5F
    // ))
    bytes32 internal constant BEBOP_DOMAIN_SEPARATOR = 0x31e9fc520926ab5a9e3842dc84bce011b96c3158dfd9cde10e518472a052d470;

    // From BebopSigning.sol:
    // keccak256("SingleOrder(uint64 partner_id,uint256 expiry,address taker_address,address maker_address,uint256 maker_nonce,address taker_token,address maker_token,uint256 taker_amount,uint256 maker_amount,address receiver,uint256 packed_commands)")
    bytes32 internal constant SINGLE_ORDER_TYPEHASH = 0xe34225bc7cd92038d42c258ee3ff66d30f9387dd932213ba32a52011df0603fc;

    function setUp() public virtual override {
        super.setUp();
        vm.label(address(BEBOP), "BebopSettlement");

        // Approve allowanceHolder to spend FROM's tokens (needed for AllowanceHolder.exec)
        safeApproveIfBelow(fromToken(), FROM, address(allowanceHolder), amount());

        // Deal maker tokens to MAKER and approve Bebop
        deal(address(toToken()), MAKER, amount() * 2);
        vm.prank(MAKER);
        toToken().approve(address(BEBOP), type(uint256).max);
    }

    /// @dev Creates a Bebop order. The order will be filled by MAKER who provides toToken()
    function _createBebopOrder(uint256 takerAmount, uint256 makerAmount)
        internal
        view
        returns (ISettlerActions.BebopOrder memory)
    {
        return ISettlerActions.BebopOrder({
            expiry: block.timestamp + 1 hours,
            maker_address: MAKER,
            maker_nonce: 1, // Must be non-zero (Bebop reverts with ZeroNonce())
            maker_token: address(toToken()),
            taker_amount: takerAmount,
            maker_amount: makerAmount,
            // Layout: unused (5 bits) | flags (3 bits) | unused (120 bits) | event_id (128 bits)
            event_id_and_flags: 12345
        });
    }

    /// @dev Computes the EIP-712 digest that Bebop will hash for signature verification.
    /// This mirrors the hash computation in BebopSigning.sol's hashSingleOrder function.
    function _computeBebopDigest(
        uint64 partnerId,
        uint256 expiry,
        address takerAddress,
        address makerAddress,
        uint256 makerNonce,
        address takerToken,
        address makerToken,
        uint256 takerAmount,
        uint256 makerAmount,
        address receiver,
        uint256 packedCommands
    ) internal pure returns (bytes32) {
        bytes32 structHash = keccak256(
            abi.encode(
                SINGLE_ORDER_TYPEHASH,
                partnerId,
                expiry,
                takerAddress,
                makerAddress,
                makerNonce,
                takerToken,
                makerToken,
                takerAmount,
                makerAmount,
                receiver,
                packedCommands
            )
        );

        return keccak256(abi.encodePacked("\x19\x01", BEBOP_DOMAIN_SEPARATOR, structHash));
    }

    /// @dev Compute expected digest for a Bebop order executed through Settler
    /// The digest is computed from the original order parameters, independent of fill amount.
    function _computeExpectedDigest(ISettlerActions.BebopOrder memory order, address recipient)
        internal
        view
        returns (bytes32)
    {
        // From Bebop.sol fastSwapSingle:
        // - taker_address = address(this) = settler
        // - packed_commands = taker << 96 (where taker = _msgSender() = FROM)
        // - receiver = recipient
        // - partner_id is always zero (Settler doesn't pass partnerId to Bebop)
        uint256 packedCommands = uint256(uint160(address(FROM))) << 96;

        return _computeBebopDigest(
            0, // partnerId is always zero
            order.expiry,
            address(settler), // taker_address is settler in fastSwapSingle
            order.maker_address,
            order.maker_nonce,
            address(fromToken()), // taker_token
            order.maker_token,
            order.taker_amount,
            order.maker_amount,
            recipient,
            packedCommands
        );
    }

    /// @dev Create a real signature using MAKER_PRIVATE_KEY.
    /// @param digest The EIP-712 digest to sign
    function _createMakerSignature(bytes32 digest) internal pure returns (ISettlerActions.BebopMakerSignature memory) {
        // Sign the digest with MAKER's private key
        (uint8 v, bytes32 r, bytes32 s) = vm.sign(MAKER_PRIVATE_KEY, digest);

        // Bebop expects 65 bytes: r (32) + s (32) + v (1)
        bytes memory sig = abi.encodePacked(r, s, v);

        return ISettlerActions.BebopMakerSignature({signatureBytes: sig, flags: 0});
    }

    function testBebop() public {
        uint256 _amount = amount();
        Settler _settler = settler;
        IERC20 _fromToken = fromToken();
        IERC20 _toToken = toToken();

        // 1:1 swap for simplicity
        ISettlerActions.BebopOrder memory order = _createBebopOrder(_amount, _amount);

        // Compute EIP-712 digest and create real signature
        bytes32 digest = _computeExpectedDigest(order, FROM);
        ISettlerActions.BebopMakerSignature memory makerSig = _createMakerSignature(digest);

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(_fromToken), _amount, 0);
        bytes memory sig = new bytes(0);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(_settler), permit, sig)),
            abi.encodeCall(ISettlerActions.BEBOP, (FROM, address(_fromToken), order, makerSig, 0))
        );

        ISettlerBase.AllowedSlippage memory allowedSlippage =
            ISettlerBase.AllowedSlippage({recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0});

        bytes memory ahData = abi.encodeCall(_settler.execute, (allowedSlippage, actions, bytes32(0)));

        uint256 beforeBalanceFrom = balanceOf(_fromToken, FROM);
        uint256 beforeBalanceTo = balanceOf(_toToken, FROM);
        uint256 beforeMakerBalanceFrom = balanceOf(_fromToken, MAKER);
        uint256 beforeMakerBalanceTo = balanceOf(_toToken, MAKER);

        vm.startPrank(FROM, FROM);
        snapStartName("allowanceHolder_bebop");
        allowanceHolder.exec(address(_settler), address(_fromToken), _amount, payable(address(_settler)), ahData);
        snapEnd();
        vm.stopPrank();

        // Verify taker received maker tokens
        uint256 afterBalanceTo = _toToken.balanceOf(FROM);
        assertEq(afterBalanceTo, beforeBalanceTo + _amount, "Taker should receive maker tokens");

        // Verify taker sent sell tokens
        uint256 afterBalanceFrom = _fromToken.balanceOf(FROM);
        assertEq(afterBalanceFrom, beforeBalanceFrom - _amount, "Taker should send sell tokens");

        // Verify maker received taker tokens
        uint256 afterMakerBalanceFrom = _fromToken.balanceOf(MAKER);
        assertEq(afterMakerBalanceFrom, beforeMakerBalanceFrom + _amount, "Maker should receive taker tokens");

        // Verify maker sent tokens
        uint256 afterMakerBalanceTo = _toToken.balanceOf(MAKER);
        assertEq(afterMakerBalanceTo, beforeMakerBalanceTo - _amount, "Maker should send maker tokens");
    }

    function testBebop_withSlippageCheck() public {
        uint256 _amount = amount();
        Settler _settler = settler;
        IERC20 _fromToken = fromToken();

        ISettlerActions.BebopOrder memory order = _createBebopOrder(_amount, _amount);

        // Compute EIP-712 digest and create real signature
        bytes32 digest = _computeExpectedDigest(order, FROM);
        ISettlerActions.BebopMakerSignature memory makerSig = _createMakerSignature(digest);

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(_fromToken), _amount, 0);
        bytes memory sig = new bytes(0);

        // Set amountOutMin slightly below maker_amount (1% tolerance)
        uint256 amountOutMin = (_amount * 99) / 100;

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(_settler), permit, sig)),
            abi.encodeCall(ISettlerActions.BEBOP, (FROM, address(_fromToken), order, makerSig, amountOutMin))
        );

        ISettlerBase.AllowedSlippage memory allowedSlippage =
            ISettlerBase.AllowedSlippage({recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0});

        bytes memory ahData = abi.encodeCall(_settler.execute, (allowedSlippage, actions, bytes32(0)));

        vm.startPrank(FROM, FROM);
        snapStartName("allowanceHolder_bebop_slippage");
        allowanceHolder.exec(address(_settler), address(_fromToken), _amount, payable(address(_settler)), ahData);
        snapEnd();
        vm.stopPrank();
    }

    function testBebop_slippageCheckFails() public {
        uint256 _amount = amount();
        Settler _settler = settler;
        IERC20 _fromToken = fromToken();

        // Order gives less than taker expects
        uint256 makerAmount = (_amount * 90) / 100; // Only 90% of expected
        ISettlerActions.BebopOrder memory order = _createBebopOrder(_amount, makerAmount);

        // Compute EIP-712 digest and create real signature
        bytes32 digest = _computeExpectedDigest(order, FROM);
        ISettlerActions.BebopMakerSignature memory makerSig = _createMakerSignature(digest);

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(_fromToken), _amount, 0);
        bytes memory sig = new bytes(0);

        // Taker expects full amount - should fail
        uint256 amountOutMin = _amount;

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(_settler), permit, sig)),
            abi.encodeCall(ISettlerActions.BEBOP, (FROM, address(_fromToken), order, makerSig, amountOutMin))
        );

        ISettlerBase.AllowedSlippage memory allowedSlippage =
            ISettlerBase.AllowedSlippage({recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0});

        bytes memory ahData = abi.encodeCall(_settler.execute, (allowedSlippage, actions, bytes32(0)));

        vm.startPrank(FROM, FROM);
        vm.expectRevert(
            abi.encodeWithSignature("TooMuchSlippage(address,uint256,uint256)", address(toToken()), amountOutMin, makerAmount)
        );
        allowanceHolder.exec(address(_settler), address(_fromToken), _amount, payable(address(_settler)), ahData);
        vm.stopPrank();
    }

    function testBebop_partialFill() public {
        uint256 _amount = amount();
        uint256 halfAmount = _amount / 2;
        Settler _settler = settler;
        IERC20 _fromToken = fromToken();
        IERC20 _toToken = toToken();

        // Order is for full amount, but we only transfer half
        ISettlerActions.BebopOrder memory order = _createBebopOrder(_amount, _amount);

        // Compute EIP-712 digest and create real signature
        // Note: The hash is computed from original order params, independent of fill amount
        bytes32 digest = _computeExpectedDigest(order, FROM);
        ISettlerActions.BebopMakerSignature memory makerSig = _createMakerSignature(digest);

        // Only transfer half the amount
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(_fromToken), halfAmount, 0);
        bytes memory sig = new bytes(0);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(_settler), permit, sig)),
            abi.encodeCall(ISettlerActions.BEBOP, (FROM, address(_fromToken), order, makerSig, 0))
        );

        ISettlerBase.AllowedSlippage memory allowedSlippage =
            ISettlerBase.AllowedSlippage({recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0});

        bytes memory ahData = abi.encodeCall(_settler.execute, (allowedSlippage, actions, bytes32(0)));

        uint256 beforeBalanceFrom = balanceOf(_fromToken, FROM);
        uint256 beforeBalanceTo = balanceOf(_toToken, FROM);

        vm.startPrank(FROM, FROM);
        snapStartName("allowanceHolder_bebop_partial");
        allowanceHolder.exec(address(_settler), address(_fromToken), halfAmount, payable(address(_settler)), ahData);
        snapEnd();
        vm.stopPrank();

        // Verify partial fill - should receive proportional maker tokens
        uint256 afterBalanceTo = _toToken.balanceOf(FROM);
        assertEq(afterBalanceTo, beforeBalanceTo + halfAmount, "Should receive proportional maker tokens");

        uint256 afterBalanceFrom = _fromToken.balanceOf(FROM);
        assertEq(afterBalanceFrom, beforeBalanceFrom - halfAmount, "Should send half of taker tokens");
    }

    /// @dev Helper to build actions that attempt to call a restricted target via BASIC
    function _buildRestrictedTargetActions(address restrictedTarget) internal pure returns (bytes[] memory) {
        return ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.BASIC, (address(0), 0, restrictedTarget, 0, ""))
        );
    }

    function testBebop_restrictedTarget_bebop() public {
        uint256 _amount = amount();
        Settler _settler = settler;
        IERC20 _fromToken = fromToken();

        bytes[] memory actions = _buildRestrictedTargetActions(address(BEBOP));

        ISettlerBase.AllowedSlippage memory allowedSlippage =
            ISettlerBase.AllowedSlippage({recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0});

        bytes memory ahData = abi.encodeCall(_settler.execute, (allowedSlippage, actions, bytes32(0)));

        vm.startPrank(FROM, FROM);
        vm.expectRevert(abi.encodeWithSignature("ConfusedDeputy()"));
        allowanceHolder.exec(address(_settler), address(_fromToken), _amount, payable(address(_settler)), ahData);
        vm.stopPrank();
    }

    function testBebop_restrictedTarget_permit2() public {
        uint256 _amount = amount();
        Settler _settler = settler;
        IERC20 _fromToken = fromToken();

        bytes[] memory actions = _buildRestrictedTargetActions(address(PERMIT2));

        ISettlerBase.AllowedSlippage memory allowedSlippage =
            ISettlerBase.AllowedSlippage({recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0});

        bytes memory ahData = abi.encodeCall(_settler.execute, (allowedSlippage, actions, bytes32(0)));

        vm.startPrank(FROM, FROM);
        vm.expectRevert(abi.encodeWithSignature("ConfusedDeputy()"));
        allowanceHolder.exec(address(_settler), address(_fromToken), _amount, payable(address(_settler)), ahData);
        vm.stopPrank();
    }

    function testBebop_restrictedTarget_allowanceHolder() public {
        uint256 _amount = amount();
        Settler _settler = settler;
        IERC20 _fromToken = fromToken();

        bytes[] memory actions = _buildRestrictedTargetActions(address(ALLOWANCE_HOLDER));

        ISettlerBase.AllowedSlippage memory allowedSlippage =
            ISettlerBase.AllowedSlippage({recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0});

        bytes memory ahData = abi.encodeCall(_settler.execute, (allowedSlippage, actions, bytes32(0)));

        vm.startPrank(FROM, FROM);
        vm.expectRevert(abi.encodeWithSignature("ConfusedDeputy()"));
        allowanceHolder.exec(address(_settler), address(_fromToken), _amount, payable(address(_settler)), ahData);
        vm.stopPrank();
    }
}
