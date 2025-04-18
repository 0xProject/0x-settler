// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISettlerBase} from "./interfaces/ISettlerBase.sol";
import {ISettlerTakerSubmitted} from "./interfaces/ISettlerTakerSubmitted.sol";
import {IAllowanceHolder} from "./allowanceholder/IAllowanceHolder.sol";

import {IDeployer} from "./deployer/IDeployer.sol";

import {DEPLOYER as DEPLOYER_ADDRESS} from "./deployer/DeployerAddress.sol";

import {Panic} from "./utils/Panic.sol";

library FastDeployer {
    function fastOwnerOf(IDeployer deployer, uint256 tokenId) internal view returns (address r) {
        assembly ("memory-safe") {
            mstore(0x00, 0x6352211e) // selector for `ownerOf(uint256)`
            mstore(0x20, tokenId)

            if iszero(staticcall(gas(), deployer, 0x1c, 0x24, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if or(gt(0x20, returndatasize()), shr(0xa0, r)) { revert(0x00, 0x00) }
            r := mload(0x00)
        }
    }

    function fastPrev(IDeployer deployer, uint128 tokenId) internal view returns (address r) {
        assembly ("memory-safe") {
            mstore(0x10, tokenId)
            mstore(0x00, 0xe2603dc200000000000000000000000000000000) // selector for `prev(uint128)` with `tokenId`'s padding

            if iszero(staticcall(gas(), deployer, 0x0c, 0x24, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if or(gt(0x20, returndatasize()), shr(0xa0, r)) { revert(0x00, 0x00) }
            r := mload(0x00)
        }
    }
}

abstract contract SettlerSwapper {
    using FastDeployer for IDeployer;

    address internal constant ALLOWANCE_HOLDER_ADDRESS = 0x0000000000001fF3684f28c67538d4D072C22734;
    IDeployer private constant _DEPLOYER = IDeployer(DEPLOYER_ADDRESS);
    uint128 private constant _SETTLER_TOKENID = 2;

    error CounterfeitSettler(ISettlerTakerSubmitted counterfeitSettler);
    error ApproveFailed(IERC20 token);

    function requireValidSettler(ISettlerTakerSubmitted settler) internal view {
        // Any revert in `ownerOf` or `prev` will be bubbled. Any error in ABIDecoding the result
        // will result in a revert without a reason string.
        if (
            _DEPLOYER.fastOwnerOf(_SETTLER_TOKENID) != address(settler)
                && _DEPLOYER.fastPrev(_SETTLER_TOKENID) != address(settler)
        ) {
            assembly ("memory-safe") {
                mstore(0x14, settler)
                mstore(0x00, 0x7a1cd8fa000000000000000000000000) // selector for `CounterfeitSettler(address)` with `settler`'s padding
                revert(0x10, 0x24)
            }
        }
    }

    modifier validSettler(ISettlerTakerSubmitted settler) {
        requireValidSettler(settler);
        _;
    }

    function _swapAll(
        ISettlerTakerSubmitted settler,
        IERC20 sellToken,
        address payable recipient,
        IERC20 buyToken,
        uint256 minAmountOut,
        bytes calldata actions,
        bytes32 zid
    ) internal {
        bool success;
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            // encode the arguments to Settler
            calldatacopy(add(0x178, ptr), actions.offset, actions.length)
            mstore(add(0x158, ptr), zid)
            mstore(add(0x138, ptr), 0xa0)
            mstore(add(0x118, ptr), minAmountOut)
            mstore(add(0xf8, ptr), buyToken)
            mstore(add(0xe4, ptr), shl(0x60, recipient)) // clears `buyToken`'s padding
            mstore(add(0xc4, ptr), 0x1fff991f000000000000000000000000) // selector for `execute((address,address,uint256),bytes[],bytes32)` with `recipient`'s padding

            function emptyRevert() {
                revert(0x00, 0x00)
            }

            for {} 1 {} {
                function bubbleRevert(p) {
                    returndatacopy(p, 0x00, returndatasize())
                    revert(p, returndatasize())
                }

                if eq(shl(0x60, sellToken), 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee000000000000000000000000) {
                    if iszero(
                        call(gas(), settler, selfbalance(), add(0xd4, ptr), add(0xa4, actions.length), 0x00, 0x20)
                    ) { bubbleRevert(ptr) }
                    if gt(0x20, returndatasize()) { emptyRevert() }
                    success := mload(0x00)
                    break
                }

                // Determine the sell amount exactly so that we can set an exact allowance. This is
                // done primarily to handle stupid tokens that don't allow you to set an allowance
                // greater than your balance. As a secondary concern, it lets us save gas by
                // collecting the refund for clearing the allowance slot during `transferFrom`.
                mstore(0x00, 0x70a08231) // selector for `balanceOf(address)`
                mstore(0x20, address())
                if iszero(staticcall(gas(), sellToken, 0x1c, 0x24, 0x40, 0x20)) { bubbleRevert(ptr) }
                if iszero(lt(0x1f, returndatasize())) { emptyRevert() }

                // Set the exact allowance on AllowanceHolder. The amount is already in memory 0x40.
                mstore(0x00, 0x095ea7b3) // selector for `approve(address,uint256)`
                mstore(0x20, ALLOWANCE_HOLDER_ADDRESS)
                if iszero(call(gas(), sellToken, 0x00, 0x1c, 0x44, 0x00, 0x20)) { bubbleRevert(ptr) }
                if iszero(or(and(eq(mload(0x00), 0x01), lt(0x1f, returndatasize())), iszero(returndatasize()))) {
                    mstore(0x14, sellToken)
                    mstore(0x00, 0xc90bb86a000000000000000000000000) // selector for `ApproveFailed(address)` with `sellToken`'s padding
                    revert(0x10, 0x24)
                }

                // length of the arguments to Settler
                mstore(add(0xb4, ptr), add(0xc4, actions.length))

                // encode the arguments to AllowanceHolder
                mstore(add(0x94, ptr), 0xa0)
                mstore(add(0x74, ptr), settler)
                mcopy(add(0x54, ptr), 0x40, 0x2c) // `sellAmount` and clears `settler`'s padding
                mstore(add(0x34, ptr), sellToken)
                mstore(add(0x20, ptr), shl(0x60, settler)) // clears `sellToken`'s padding
                mstore(ptr, 0x2213bc0b000000000000000000000000) // selector for `exec(address,address,uint256,address,bytes)` with `settler`'s padding

                if iszero(
                    call(gas(), ALLOWANCE_HOLDER_ADDRESS, 0x00, add(0x10, ptr), add(0x168, actions.length), 0x00, 0x60)
                ) { bubbleRevert(ptr) }
                if gt(0x60, returndatasize()) { emptyRevert() }
                success := mload(0x40)

                mstore(0x40, ptr)
                break
            }

            if shr(0x01, success) { emptyRevert() }
        }
        if (!success) {
            Panic.panic(Panic.GENERIC);
        }
    }

    function _swap(
        ISettlerTakerSubmitted settler,
        IERC20 sellToken,
        uint256 sellAmount,
        ISettlerBase.AllowedSlippage calldata slippage,
        bytes calldata actions,
        bytes32 zid
    ) internal {
        bool success;
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            // encode the arguments to Settler
            calldatacopy(add(0x178, ptr), actions.offset, actions.length)
            mstore(add(0x158, ptr), zid)
            mstore(add(0x138, ptr), 0xa0)
            calldatacopy(add(0xc8, ptr), slippage, 0x60)
            mstore(add(0xc4, ptr), 0x1fff991f) // selector for `execute((address,address,uint256),bytes[],bytes32)`

            function emptyRevert() {
                revert(0x00, 0x00)
            }

            for {} 1 {} {
                function bubbleRevert(p) {
                    returndatacopy(p, 0x00, returndatasize())
                    revert(p, returndatasize())
                }

                if eq(shl(0x60, sellToken), 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee000000000000000000000000) {
                    if iszero(
                        call(gas(), settler, selfbalance(), add(0xd4, ptr), add(0xa4, actions.length), 0x00, 0x20)
                    ) { bubbleRevert(ptr) }
                    if gt(0x20, returndatasize()) { emptyRevert() }
                    success := mload(0x00)
                    break
                }

                // set the exact allowance on AllowanceHolder
                mstore(0x00, 0x095ea7b3) // selector for `approve(address,uint256)`
                mstore(0x20, ALLOWANCE_HOLDER_ADDRESS)
                mstore(0x40, sellAmount)
                if iszero(call(gas(), sellToken, 0x00, 0x1c, 0x44, 0x00, 0x20)) { bubbleRevert(ptr) }
                if iszero(or(and(eq(mload(0x00), 0x01), lt(0x1f, returndatasize())), iszero(returndatasize()))) {
                    mstore(0x14, sellToken)
                    mstore(0x00, 0xc90bb86a000000000000000000000000) // selector for `ApproveFailed(address)` with `sellToken`'s padding
                    revert(0x10, 0x24)
                }

                // length of the arguments to Settler
                mstore(add(0xb4, ptr), add(0xc4, actions.length))

                // encode the arguments to AllowanceHolder
                mstore(add(0x94, ptr), 0xa0)
                mstore(add(0x74, ptr), settler)
                mcopy(add(0x54, ptr), 0x40, 0x2c) // `sellAmount` and clears `settler`'s padding
                mstore(add(0x34, ptr), sellToken)
                mstore(add(0x20, ptr), shl(0x60, settler)) // clears `sellToken`'s padding
                mstore(ptr, 0x2213bc0b000000000000000000000000) // selector for `exec(address,address,uint256,address,bytes)` with `settler`'s padding

                if iszero(
                    call(gas(), ALLOWANCE_HOLDER_ADDRESS, 0x00, add(0x10, ptr), add(0x168, actions.length), 0x00, 0x60)
                ) { bubbleRevert(ptr) }
                if gt(0x60, returndatasize()) { emptyRevert() }
                success := mload(0x40)

                mstore(0x40, ptr)
                break
            }

            if shr(0x01, success) { emptyRevert() }
        }
        if (!success) {
            Panic.panic(Panic.GENERIC);
        }
    }
}
