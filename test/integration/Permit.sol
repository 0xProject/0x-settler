// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";
import {IERC2612, IERC20PermitAllowed} from "src/interfaces/IERC2612.sol";
import {IERC20MetaTransaction} from "src/interfaces/INativeMetaTransaction.sol";
import {Permit} from "src/core/Permit.sol";

contract PermitTest is SettlerBasePairTest {
    IERC2612 internal constant USDC = IERC2612(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48);
    IERC20PermitAllowed internal constant DAI = IERC20PermitAllowed(0x6B175474E89094C44Da98b954EedeAC495271d0F);
    IERC20MetaTransaction internal constant ZED = IERC20MetaTransaction(0x5eC03C1f7fA7FF05EC476d19e34A22eDDb48ACdc);

    bytes32 private constant _PERMIT_TYPEHASH =
        keccak256("Permit(address owner,address spender,uint256 value,uint256 nonce,uint256 deadline)");

    bytes32 private constant _PERMIT_ALLOWED_TYPEHASH =
        keccak256("Permit(address holder,address spender,uint256 nonce,uint256 expiry,bool allowed)");

    bytes32 private constant _META_TRANSACTION_TYPEHASH =
        keccak256("MetaTransaction(uint256 nonce,address from,bytes functionSignature)");

    function _testName() internal pure override returns (string memory) {
        return "ERC2612Funding";
    }

    function fromToken() internal pure override returns (IERC20) {}

    function toToken() internal pure override returns (IERC20) {}

    function amount() internal pure override returns (uint256) {
        return 1000e6;
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

    function _signPermitAllowed(
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
        uint256 nonce = ZED.getNonce(owner);
        bytes32 domainSeparator = ZED.getDomainSeparator();

        bytes32 structHash = keccak256(
            abi.encode(
                _META_TRANSACTION_TYPEHASH, nonce, owner, keccak256(abi.encodeCall(ZED.approve, (spender, amount)))
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
            abi.encodePacked(Permit.PermitType.ERC2612, abi.encode(sender, amount(), deadline, v, r, s));

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.TRANSFER_FROM_WITH_PERMIT,
                (address(this), defaultERC20PermitTransfer(address(USDC), amount(), 0), permitData)
            )
        );

        vm.prank(sender);
        allowanceHolder.exec(
            address(settler),
            address(USDC),
            amount(),
            payable(address(settler)),
            abi.encodeCall(
                settler.execute,
                (
                    ISettlerBase.AllowedSlippage({
                        recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
                    }),
                    actions,
                    bytes32(0)
                )
            )
        );

        assertEq(USDC.balanceOf(address(this)), amount(), "Transfer failed");
        assertEq(USDC.balanceOf(sender), 0, "Sender should have 0 balance");
    }

    function testPermitAllowed() public {
        (address sender, uint256 pk) = makeAddrAndKey("sender");

        deal(address(DAI), sender, amount());

        uint256 expiry = block.timestamp + 1 hours;
        uint256 nonce = DAI.nonces(sender);
        (uint8 v, bytes32 r, bytes32 s) = _signPermitAllowed(sender, address(allowanceHolder), nonce, expiry, true, pk);

        bytes memory permitData =
            abi.encodePacked(Permit.PermitType.PermitAllowed, abi.encode(sender, nonce, expiry, true, v, r, s));

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.TRANSFER_FROM_WITH_PERMIT,
                (address(this), defaultERC20PermitTransfer(address(DAI), amount(), 0), permitData)
            )
        );

        vm.prank(sender);
        allowanceHolder.exec(
            address(settler),
            address(DAI),
            amount(),
            payable(address(settler)),
            abi.encodeCall(
                settler.execute,
                (
                    ISettlerBase.AllowedSlippage({
                        recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
                    }),
                    actions,
                    bytes32(0)
                )
            )
        );

        assertEq(DAI.balanceOf(address(this)), amount(), "Transfer failed");
        assertEq(DAI.balanceOf(sender), 0, "Sender should have 0 balance");
    }

    function testNativeMetaTransaction() public {
        (address sender, uint256 pk) = makeAddrAndKey("sender");

        deal(address(ZED), sender, amount());

        (uint8 v, bytes32 r, bytes32 s) = _signNativeMetaTransaction(sender, address(allowanceHolder), amount(), pk);

        bytes memory permitData =
            abi.encodePacked(Permit.PermitType.NativeMetaTransaction, abi.encode(sender, amount(), v, r, s));

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.TRANSFER_FROM_WITH_PERMIT,
                (address(this), defaultERC20PermitTransfer(address(ZED), amount(), 0), permitData)
            )
        );

        vm.prank(sender);
        allowanceHolder.exec(
            address(settler),
            address(ZED),
            amount(),
            payable(address(settler)),
            abi.encodeCall(
                settler.execute,
                (
                    ISettlerBase.AllowedSlippage({
                        recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
                    }),
                    actions,
                    bytes32(0)
                )
            )
        );

        assertEq(ZED.balanceOf(address(this)), amount(), "Transfer failed");
        assertEq(ZED.balanceOf(sender), 0, "Sender should have 0 balance");
    }
}
