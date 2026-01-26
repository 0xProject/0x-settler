// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";
import {IERC2612, IDAIStylePermit} from "src/interfaces/IERC2612.sol";
import {IERC20MetaTransaction} from "src/interfaces/INativeMetaTransaction.sol";
import {Permit} from "src/core/Permit.sol";
import {PermitFailed} from "src/core/SettlerErrors.sol";
import {PolygonSettler as Settler} from "src/chains/Polygon/TakerSubmitted.sol";

contract PermitTest is SettlerBasePairTest {
    IERC2612 internal constant USDC = IERC2612(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48);
    IDAIStylePermit internal constant DAI = IDAIStylePermit(0x6B175474E89094C44Da98b954EedeAC495271d0F);
    IERC20MetaTransaction internal constant ROUTE = IERC20MetaTransaction(0x16ECCfDbb4eE1A85A33f3A9B21175Cd7Ae753dB4);

    bytes32 private constant _PERMIT_TYPEHASH =
        keccak256("Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)");

    bytes32 private constant _PERMIT_ALLOWED_TYPEHASH =
        keccak256("Permit(address holder,address spender,uint256 nonce,uint256 expiry,bool allowed)");

    bytes32 private constant _META_TRANSACTION_TYPEHASH =
        keccak256("MetaTransaction(uint256 nonce,address from,bytes functionSignature)");

    function settlerInitCode() internal virtual override returns (bytes memory) {
        return bytes.concat(type(Settler).creationCode, abi.encode(bytes20(0)));
    }

    function _testName() internal pure override returns (string memory) {
        return "transfer-from-with-permit";
    }

    function fromToken() internal pure override returns (IERC20) {}

    function toToken() internal pure override returns (IERC20) {}

    function amount() internal pure override returns (uint256) {
        return 1000e6;
    }

    function _vs(uint256 v, bytes32 s) internal view returns (bytes32 vs) {
        return bytes32(v - 27) << 255 | s;
    }

    function _signERC2612Permit(address owner, address spender, uint256 value, uint256 deadline, uint256 privateKey)
        internal
        view
        returns (uint8 v, bytes32 r, bytes32 s)
    {
        uint256 nonce = USDC.nonces(owner);
        bytes32 domainSeparator = USDC.DOMAIN_SEPARATOR();

        bytes32 structHash = keccak256(abi.encode(_PERMIT_TYPEHASH, owner, spender, value, nonce, deadline));

        bytes32 digest = keccak256(abi.encodePacked("\x19\x01", domainSeparator, structHash));

        (v, r, s) = vm.sign(privateKey, digest);
    }

    function _signDAIPermit(
        address holder,
        address spender,
        uint256 nonce,
        uint256 expiry,
        bool allowed,
        uint256 privateKey
    ) internal view returns (uint8 v, bytes32 r, bytes32 s) {
        bytes32 domainSeparator = DAI.DOMAIN_SEPARATOR();

        bytes32 structHash = keccak256(abi.encode(_PERMIT_ALLOWED_TYPEHASH, holder, spender, nonce, expiry, allowed));

        bytes32 digest = keccak256(abi.encodePacked("\x19\x01", domainSeparator, structHash));

        (v, r, s) = vm.sign(privateKey, digest);
    }

    function _signNativeMetaTransaction(address owner, address spender, uint256 amount, uint256 privateKey)
        internal
        view
        returns (uint8 v, bytes32 r, bytes32 s)
    {
        uint256 nonce = ROUTE.getNonce(owner);
        bytes32 domainSeparator = ROUTE.getDomainSeperator();

        bytes32 structHash = keccak256(
            abi.encode(
                _META_TRANSACTION_TYPEHASH, nonce, owner, keccak256(abi.encodeCall(ROUTE.approve, (spender, amount)))
            )
        );

        bytes32 digest = keccak256(abi.encodePacked("\x19\x01", domainSeparator, structHash));

        (v, r, s) = vm.sign(privateKey, digest);
    }

    function testPermit() public {
        (address sender, uint256 pk) = makeAddrAndKey("sender");

        deal(address(USDC), sender, amount());

        uint256 deadline = block.timestamp + 1 hours;
        (uint8 v, bytes32 r, bytes32 s) = _signERC2612Permit(sender, address(allowanceHolder), amount(), deadline, pk);

        bytes memory permitData =
            abi.encodePacked(Permit.PermitType.ERC2612, abi.encode(amount(), deadline, r, _vs(v, s)));

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.TRANSFER_FROM,
                (address(this), defaultERC20PermitTransfer(address(USDC), amount(), 0), bytes(""))
            )
        );

        uint256 snapshot = vm.snapshot();

        vm.prank(sender);
        snapStartName("ERC2612");
        allowanceHolder.exec(
            address(settler),
            address(USDC),
            amount(),
            payable(address(settler)),
            abi.encodeCall(
                settler.executeWithPermit,
                (
                    ISettlerBase.AllowedSlippage({
                        recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
                    }),
                    actions,
                    bytes32(0),
                    permitData
                )
            )
        );
        snapEnd();

        assertEq(USDC.balanceOf(address(this)), amount(), "Transfer failed");
        assertEq(USDC.balanceOf(sender), 0, "Sender should have 0 balance");

        vm.revertTo(snapshot);

        // Front-running the permit
        USDC.permit(sender, address(allowanceHolder), amount(), deadline, v, r, s);

        vm.prank(sender);
        allowanceHolder.exec(
            address(settler),
            address(USDC),
            amount(),
            payable(address(settler)),
            abi.encodeCall(
                settler.executeWithPermit,
                (
                    ISettlerBase.AllowedSlippage({
                        recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
                    }),
                    actions,
                    bytes32(0),
                    permitData
                )
            )
        );

        assertEq(USDC.balanceOf(address(this)), amount(), "Transfer failed when permit was front-run");
        assertEq(USDC.balanceOf(sender), 0, "Sender should have 0 balance when permit was front-run");

        // resubmitting should fail because the nonce in the signature is now incorrect
        vm.expectRevert(PermitFailed.selector);
        vm.prank(sender);
        allowanceHolder.exec(
            address(settler),
            address(USDC),
            amount(),
            payable(address(settler)),
            abi.encodeCall(
                settler.executeWithPermit,
                (
                    ISettlerBase.AllowedSlippage({
                        recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
                    }),
                    actions,
                    bytes32(0),
                    permitData
                )
            )
        );
    }

    function testDAIPermit() public {
        (address sender, uint256 pk) = makeAddrAndKey("sender");

        deal(address(DAI), sender, amount());

        uint256 expiry = block.timestamp + 1 hours;
        uint256 nonce = DAI.nonces(sender);
        (uint8 v, bytes32 r, bytes32 s) = _signDAIPermit(sender, address(allowanceHolder), nonce, expiry, true, pk);

        bytes memory permitData =
            abi.encodePacked(Permit.PermitType.DAIPermit, abi.encode(nonce, expiry, true, r, _vs(v, s)));

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.TRANSFER_FROM,
                (address(this), defaultERC20PermitTransfer(address(DAI), amount(), 0), bytes(""))
            )
        );

        uint256 snapshot = vm.snapshot();

        vm.prank(sender);
        snapStartName("DAIPermit");
        allowanceHolder.exec(
            address(settler),
            address(DAI),
            amount(),
            payable(address(settler)),
            abi.encodeCall(
                settler.executeWithPermit,
                (
                    ISettlerBase.AllowedSlippage({
                        recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
                    }),
                    actions,
                    bytes32(0),
                    permitData
                )
            )
        );
        snapEnd();
        
        assertEq(DAI.balanceOf(address(this)), amount(), "Transfer failed");
        assertEq(DAI.balanceOf(sender), 0, "Sender should have 0 balance");

        vm.revertTo(snapshot);

        // Front-running the permit
        DAI.permit(sender, address(allowanceHolder), nonce, expiry, true, v, r, s);

        vm.prank(sender);
        allowanceHolder.exec(
            address(settler),
            address(DAI),
            amount(),
            payable(address(settler)),
            abi.encodeCall(
                settler.executeWithPermit,
                (
                    ISettlerBase.AllowedSlippage({
                        recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
                    }),
                    actions,
                    bytes32(0),
                    permitData
                )
            )
        );

        assertEq(DAI.balanceOf(address(this)), amount(), "Transfer failed when permit was front-run");
        assertEq(DAI.balanceOf(sender), 0, "Sender should have 0 balance when permit was front-run");

        // resubmitting should fail because the nonce in the signature is now incorrect
        // validation succeds anyway because the allowance is there given that in DAI it is type(uint256).max
        // should fail attempting to do the transfer because there is no enough balance to transfer
        vm.expectRevert("Dai/insufficient-balance");
        vm.prank(sender);
        allowanceHolder.exec(
            address(settler),
            address(DAI),
            amount(),
            payable(address(settler)),
            abi.encodeCall(
                settler.executeWithPermit,
                (
                    ISettlerBase.AllowedSlippage({
                        recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
                    }),
                    actions,
                    bytes32(0),
                    permitData
                )
            )
        );
    }

    function testNativeMetaTransaction() public {
        (address sender, uint256 pk) = makeAddrAndKey("sender");

        deal(address(ROUTE), sender, amount());

        (uint8 v, bytes32 r, bytes32 s) = _signNativeMetaTransaction(sender, address(allowanceHolder), amount(), pk);

        bytes memory permitData =
            abi.encodePacked(Permit.PermitType.NativeMetaTransaction, abi.encode(amount(), r, _vs(v, s)));

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.TRANSFER_FROM,
                (address(this), defaultERC20PermitTransfer(address(ROUTE), amount(), 0), bytes(""))
            )
        );

        uint256 snapshot = vm.snapshot();

        vm.prank(sender);
        snapStartName("NativeMetaTransaction");
        allowanceHolder.exec(
            address(settler),
            address(ROUTE),
            amount(),
            payable(address(settler)),
            abi.encodeCall(
                settler.executeWithPermit,
                (
                    ISettlerBase.AllowedSlippage({
                        recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
                    }),
                    actions,
                    bytes32(0),
                    permitData
                )
            )
        );
        snapEnd();

        assertEq(ROUTE.balanceOf(address(this)), amount(), "Transfer failed");
        assertEq(ROUTE.balanceOf(sender), 0, "Sender should have 0 balance");

        vm.revertTo(snapshot);

        // Front-running the executeMetaTransaction
        ROUTE.executeMetaTransaction(
            sender, abi.encodeCall(ROUTE.approve, (address(allowanceHolder), amount())), r, s, v
        );

        vm.prank(sender);
        allowanceHolder.exec(
            address(settler),
            address(ROUTE),
            amount(),
            payable(address(settler)),
            abi.encodeCall(
                settler.executeWithPermit,
                (
                    ISettlerBase.AllowedSlippage({
                        recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
                    }),
                    actions,
                    bytes32(0),
                    permitData
                )
            )
        );

        assertEq(ROUTE.balanceOf(address(this)), amount(), "Transfer failed when executeMetaTransaction was front-run");
        assertEq(ROUTE.balanceOf(sender), 0, "Sender should have 0 balance when executeMetaTransaction was front-run");

        // resubmitting should fail because the nonce in the signature is now incorrect
        vm.expectRevert(PermitFailed.selector);
        vm.prank(sender);
        allowanceHolder.exec(
            address(settler),
            address(ROUTE),
            amount(),
            payable(address(settler)),
            abi.encodeCall(
                settler.executeWithPermit,
                (
                    ISettlerBase.AllowedSlippage({
                        recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
                    }),
                    actions,
                    bytes32(0),
                    permitData
                )
            )
        );
    }

    function testUnsupportedPermitType() public {
        (address sender, uint256 pk) = makeAddrAndKey("sender");

        (uint8 v, bytes32 r, bytes32 s) = _signERC2612Permit(sender, address(allowanceHolder), 0, 0, pk);

        bytes memory permitData = abi.encodePacked(uint8(4));

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.TRANSFER_FROM,
                (address(this), defaultERC20PermitTransfer(address(USDC), amount(), 0), bytes(""))
            )
        );

        vm.prank(sender);
        vm.expectRevert(abi.encodeWithSignature("Panic(uint256)", 0x21));
        allowanceHolder.exec(
            address(settler),
            address(USDC),
            amount(),
            payable(address(settler)),
            abi.encodeCall(
                settler.executeWithPermit,
                (
                    ISettlerBase.AllowedSlippage({
                        recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
                    }),
                    actions,
                    bytes32(0),
                    permitData
                )
            )
        );
    }
}
