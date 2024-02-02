// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {IERC20} from "../../src/IERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";
import {ICurveV2Pool} from "./vendor/ICurveV2Pool.sol";
import {IZeroEx} from "./vendor/IZeroEx.sol";

import {LibBytes} from "../utils/LibBytes.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";

import {SafeTransferLib} from "../../src/utils/SafeTransferLib.sol";

import {IAllowanceHolder} from "../../src/allowanceholder/IAllowanceHolder.sol";
import {Settler} from "../../src/Settler.sol";
import {ISettlerActions} from "../../src/ISettlerActions.sol";
import {OtcOrderSettlement} from "../../src/core/OtcOrderSettlement.sol";

abstract contract AllowanceHolderPairTest is SettlerBasePairTest {
    using SafeTransferLib for IERC20;
    using LibBytes for bytes;

    function setUp() public virtual override {
        super.setUp();
        // Trusted Forwarder / Allowance Holder
        safeApproveIfBelow(fromToken(), FROM, address(allowanceHolder), amount());
    }

    function uniswapV3Path() internal virtual returns (bytes memory);

    function testAllowanceHolder_uniswapV3() public {
        bytes[] memory actions = ActionDataBuilder.build(
            // Perform a transfer into Settler via AllowanceHolder
            abi.encodeCall(
                ISettlerActions.PERMIT2_TRANSFER_FROM,
                (
                    address(settler),
                    defaultERC20PermitTransfer(address(fromToken()), amount(), 0 /* nonce */ ),
                    new bytes(0) /* sig (empty) */
                )
            ),
            // Execute UniswapV3 from the Settler balance
            abi.encodeCall(ISettlerActions.UNISWAPV3_SWAP_EXACT_IN, (FROM, 10_000, 0, uniswapV3Path()))
        );

        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        //_warm_allowanceHolder_slots(address(fromToken()), amount());

        vm.startPrank(FROM, FROM); // prank both msg.sender and tx.origin
        snapStartName("allowanceHolder_uniswapV3");
        //_cold_account_access();

        _allowanceHolder.exec(
            address(_settler),
            address(fromToken()),
            amount(),
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
                // Perform a transfer into directly to the UniswapV3 pool via AllowanceHolder on demand
                ISettlerActions.UNISWAPV3_PERMIT2_SWAP_EXACT_IN,
                (
                    FROM,
                    amount(),
                    0,
                    uniswapV3Path(),
                    defaultERC20PermitTransfer(address(fromToken()), amount(), 0 /* nonce */ ),
                    new bytes(0) // sig (empty)
                )
            )
        );

        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        //_warm_allowanceHolder_slots(address(fromToken()), amount());

        vm.startPrank(FROM, FROM); // prank both msg.sender and tx.origin
        snapStartName("allowanceHolder_uniswapV3VIP");
        //_cold_account_access();

        _allowanceHolder.exec(
            address(_settler),
            address(fromToken()),
            amount(),
            payable(address(_settler)),
            abi.encodeCall(
                _settler.execute,
                (actions, Settler.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0 ether}))
            )
        );
        snapEnd();
    }

    function testAllowanceHolder_uniswapV3VIP_contract() public {
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                // Perform a transfer into directly to the UniswapV3 pool via AllowanceHolder on demand
                ISettlerActions.UNISWAPV3_PERMIT2_SWAP_EXACT_IN,
                (
                    FROM,
                    amount(),
                    0,
                    uniswapV3Path(),
                    defaultERC20PermitTransfer(address(fromToken()), amount(), 0 /* nonce */ ),
                    new bytes(0) // sig (empty)
                )
            )
        );

        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        //_warm_allowanceHolder_slots(address(fromToken()), amount());

        vm.startPrank(FROM); // Do not prank tx.origin, msg.sender != tx.origin
        snapStartName("allowanceHolder_uniswapV3VIP_contract");
        //_cold_account_access();

        _allowanceHolder.exec(
            address(_settler),
            address(fromToken()),
            amount(),
            payable(address(_settler)),
            abi.encodeCall(
                _settler.execute,
                (actions, Settler.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0 ether}))
            )
        );
        snapEnd();
    }

    /// @dev With a future deployment with EIP1153 these storage slots will be transient
    /// and therefor cost the same as if they were already warm
    /// TODO should we keep this on of have it as a flag if we deploy prior to EIP1153
    function _warm_allowanceHolder_slots(address token, uint256 amount) internal {
        bytes32 allowedSlot = keccak256(abi.encodePacked(address(settler), FROM, token));
        bytes32 allowedValue = bytes32(amount);
        vm.store(address(allowanceHolder), allowedSlot, allowedValue);
    }

    function _cold_account_access() internal {
        // `_warm_allowanceHolder_slots` also warms the whole `AllowanceHolder`
        // account. in order to pretend that we didn't just do that, we do a
        // cold account access inside the metered path. this costs an
        // erroneously-extra 100 gas.
        assembly ("memory-safe") {
            let _pop := call(gas(), 0xdead, 0, 0x00, 0x00, 0x00, 0x00)
        }
    }
}
