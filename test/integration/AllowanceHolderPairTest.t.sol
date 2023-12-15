// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {IERC20} from "../../src/IERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

import {BasePairTest} from "./BasePairTest.t.sol";
import {ICurveV2Pool} from "./vendor/ICurveV2Pool.sol";
import {IZeroEx} from "./vendor/IZeroEx.sol";

import {LibBytes} from "../utils/LibBytes.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";

import {SafeTransferLib} from "../../src/utils/SafeTransferLib.sol";

import {AllowanceHolder} from "../../src/AllowanceHolder.sol";
import {Settler} from "../../src/Settler.sol";
import {ISettlerActions} from "../../src/ISettlerActions.sol";
import {OtcOrderSettlement} from "../../src/core/OtcOrderSettlement.sol";

abstract contract AllowanceHolderPairTest is BasePairTest {
    using SafeTransferLib for IERC20;
    using LibBytes for bytes;

    Settler private settler;
    AllowanceHolder private allowanceHolder;

    function setUp() public virtual override {
        super.setUp();
        (settler, allowanceHolder) = getAllowanceHolder();
        // Trusted Forwarder / Allowance Holder
        safeApproveIfBelow(fromToken(), FROM, address(allowanceHolder), amount());
    }

    function uniswapV3Path() internal virtual returns (bytes memory);

    function getAllowanceHolder() internal returns (Settler _settler, AllowanceHolder _allowanceHolder) {
        _allowanceHolder = new AllowanceHolder();
        _settler = new Settler(
            address(PERMIT2),
            address(address(0)), // ZeroEx
            0x1F98431c8aD98523631AE4a59f267346ea31F984, // UniV3 Factory
            0xe34f199b19b2b4f47f68442619d555527d244f78a3297ea89325f843f87b8b54, // UniV3 pool init code hash
            0x2222222222222222222222222222222222222222, // fee recipient
            address(_allowanceHolder)
        );
    }

    function _warm_allowanceHolder_slots(address token, uint256 amount) internal {
        bytes32 operatorSlot = bytes32(uint256(0x010000000000000000000000000000000000000000));
        bytes32 operatorValue = bytes32(uint256(uint160(address(settler))));
        bytes32 allowedSlot = bytes32(uint256(uint160(token)));
        bytes32 allowedValue = bytes32(amount);
        vm.store(address(allowanceHolder), operatorSlot, operatorValue);
        vm.store(address(allowanceHolder), allowedSlot, allowedValue);
    }

    function testAllowanceHolder_uniswapV3() public {
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.PERMIT2_TRANSFER_FROM,
                (address(settler), defaultERC20PermitTransfer(address(fromToken()), amount(), 0), new bytes(0))
            ),
            abi.encodeCall(ISettlerActions.UNISWAPV3_SWAP_EXACT_IN, (FROM, 10_000, 0, uniswapV3Path()))
        );

        _warm_allowanceHolder_slots(address(fromToken()), amount());

        AllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        ISignatureTransfer.TokenPermissions[] memory permits = new ISignatureTransfer.TokenPermissions[](1);
        permits[0] = ISignatureTransfer.TokenPermissions({token: address(fromToken()), amount: amount()});
        vm.startPrank(FROM, FROM); // prank both msg.sender and tx.origin

        snapStartName("allowanceHolder_uniswapV3");

        // `_warm_allowanceHolder_slots` also warms the whole `AllowanceHolder`
        // account. in order to pretend that we didn't just do that, we do a
        // cold account access inside the metered path. this costs an
        // erroneously-extra 100 gas.
        assembly ("memory-safe") {
            let _pop := call(gas(), 0xdead, 0, 0x00, 0x00, 0x00, 0x00)
        }

        _allowanceHolder.execute(
            address(_settler),
            permits,
            payable(address(_settler)),
            abi.encodeCall(
                _settler.execute,
                (actions, Settler.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0 ether}))
            )
        );
        snapEnd();
    }

    function testAllowanceHolder_uniswapV3VIP() public {
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.UNISWAPV3_PERMIT2_SWAP_EXACT_IN,
                (
                    FROM,
                    amount(),
                    0,
                    uniswapV3Path(),
                    defaultERC20PermitTransfer(address(fromToken()), amount(), 0),
                    new bytes(0)
                )
            )
        );

        _warm_allowanceHolder_slots(address(fromToken()), amount());

        AllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        ISignatureTransfer.TokenPermissions[] memory permits = new ISignatureTransfer.TokenPermissions[](1);
        permits[0] = ISignatureTransfer.TokenPermissions({token: address(fromToken()), amount: amount()});
        vm.startPrank(FROM, FROM); // prank both msg.sender and tx.origin

        snapStartName("allowanceHolder_uniswapV3VIP");

        // `_warm_allowanceHolder_slots` also warms the whole `AllowanceHolder`
        // account. in order to pretend that we didn't just do that, we do a
        // cold account access inside the metered path. this costs an
        // erroneously-extra 100 gas.
        assembly ("memory-safe") {
            let _pop := call(gas(), 0xdead, 0, 0x00, 0x00, 0x00, 0x00)
        }

        _allowanceHolder.execute(
            address(_settler),
            permits,
            payable(address(_settler)),
            abi.encodeCall(
                _settler.execute,
                (actions, Settler.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0 ether}))
            )
        );
        snapEnd();
    }

    function testAllowanceHolder_single_uniswapV3VIP() public {
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.UNISWAPV3_PERMIT2_SWAP_EXACT_IN,
                (
                    FROM,
                    amount(),
                    0,
                    uniswapV3Path(),
                    defaultERC20PermitTransfer(address(fromToken()), amount(), 0),
                    new bytes(0)
                )
            )
        );

        _warm_allowanceHolder_slots(address(fromToken()), amount());

        AllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        ISignatureTransfer.TokenPermissions memory permit =
            ISignatureTransfer.TokenPermissions({token: address(fromToken()), amount: amount()});
        vm.startPrank(FROM, FROM); // prank both msg.sender and tx.origin

        snapStartName("allowanceHolder_single_uniswapV3VIP");

        // `_warm_allowanceHolder_slots` also warms the whole `AllowanceHolder`
        // account. in order to pretend that we didn't just do that, we do a
        // cold account access inside the metered path. this costs an
        // erroneously-extra 100 gas.
        assembly ("memory-safe") {
            let _pop := call(gas(), 0xdead, 0, 0x00, 0x00, 0x00, 0x00)
        }

        _allowanceHolder.execute(
            address(_settler),
            permit,
            payable(address(_settler)),
            abi.encodeCall(
                _settler.execute,
                (actions, Settler.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0 ether}))
            )
        );
        snapEnd();
    }

    function testAllowanceHolder_moveExecute_uniswapV3() public {
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.UNISWAPV3_SWAP_EXACT_IN, (FROM, 10_000, 0, uniswapV3Path()))
        );

        _warm_allowanceHolder_slots(address(fromToken()), amount());

        AllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        ISignatureTransfer.TokenPermissions[] memory permits = new ISignatureTransfer.TokenPermissions[](1);
        permits[0] = ISignatureTransfer.TokenPermissions({token: address(fromToken()), amount: amount()});
        vm.startPrank(FROM, FROM); // prank both msg.sender and tx.origin

        snapStartName("allowanceHolder_moveExecute_uniswapV3");

        // `_warm_allowanceHolder_slots` also warms the whole `AllowanceHolder`
        // account. in order to pretend that we didn't just do that, we do a
        // cold account access inside the metered path. this costs an
        // erroneously-extra 100 gas.
        assembly ("memory-safe") {
            let _pop := call(gas(), 0xdead, 0, 0x00, 0x00, 0x00, 0x00)
        }

        _allowanceHolder.moveExecute(
            permits,
            payable(address(_settler)),
            abi.encodeCall(
                _settler.execute,
                (actions, Settler.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0 ether}))
            )
        );
        snapEnd();
    }
}
