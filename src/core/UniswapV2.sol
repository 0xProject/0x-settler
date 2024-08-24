// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "forge-std/interfaces/IERC20.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {Panic} from "../utils/Panic.sol";
import {TooMuchSlippage} from "./SettlerErrors.sol";

import {SettlerAbstract} from "../SettlerAbstract.sol";

interface IUniV2Pair {
    function token0() external view returns (address);

    function token1() external view returns (address);

    function getReserves() external view returns (uint112, uint112, uint32);

    function swap(uint256, uint256, address, bytes calldata) external;
}

abstract contract UniswapV2 is SettlerAbstract {
    using UnsafeMath for uint256;

    // bytes4(keccak256("getReserves()"))
    uint32 private constant UNI_PAIR_RESERVES_SELECTOR = 0x0902f1ac;
    // bytes4(keccak256("swap(uint256,uint256,address,bytes)"))
    uint32 private constant UNI_PAIR_SWAP_SELECTOR = 0x022c0d9f;
    // bytes4(keccak256("transfer(address,uint256)"))
    uint32 private constant ERC20_TRANSFER_SELECTOR = 0xa9059cbb;
    // bytes4(keccak256("balanceOf(address)"))
    uint32 private constant ERC20_BALANCEOF_SELECTOR = 0x70a08231;

    /// @dev Sell a token for another token using UniswapV2.
    function sellToUniswapV2(
        address recipient,
        address sellToken,
        uint256 bps,
        address pool,
        uint24 swapInfo,
        uint256 minBuyAmount
    ) internal {
        // Preventing calls to Permit2 or AH is not explicitly required as neither of these contracts implement the `swap` nor `transfer` selector

        // |7|6|5|4|3|2|1|0| - bit positions in swapInfo (uint8)
        // |0|0|0|0|0|0|F|Z| - Z: zeroForOne flag, F: sellTokenHasFee flag
        bool zeroForOne = (swapInfo & 1) == 1; // Extract the least significant bit (bit 0)
        bool sellTokenHasFee = (swapInfo & 2) >> 1 == 1; // Extract the second least significant bit (bit 1) and shift it right
        uint256 feeBps = swapInfo >> 8;

        uint256 sellAmount;
        uint256 buyAmount;
        // If bps is zero we assume there are no funds within this contract, skip the updating sellAmount.
        // This case occurs if the pool is being chained, in which the funds have been sent directly to the pool
        if (bps != 0) {
            // We don't care about phantom overflow here because reserves are
            // limited to 112 bits. Any token balance that would overflow here would
            // also break UniV2.
            // It is *possible* to set `bps` above the basis and therefore
            // cause an overflow on this multiplication. However, `bps` is
            // passed as authenticated calldata, so this is a GIGO error that we
            // do not attempt to fix.
            unchecked {
                sellAmount = (IERC20(sellToken).balanceOf(address(this)) * bps).unsafeDiv(BASIS);
            }
        }
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            // transfer sellAmount (a non zero amount) of sellToken to the pool
            if sellAmount {
                mstore(ptr, ERC20_TRANSFER_SELECTOR)
                mstore(add(ptr, 0x20), pool)
                mstore(add(ptr, 0x40), sellAmount)
                // ...||ERC20_TRANSFER_SELECTOR|pool|sellAmount|
                if iszero(call(gas(), sellToken, 0, add(ptr, 0x1c), 0x44, 0x00, 0x20)) { bubbleRevert(ptr) }
                if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 0x20)), eq(mload(0x00), 1)))) {
                    revert(0, 0)
                }
            }

            // get pool reserves
            let sellReserve
            let buyReserve
            mstore(0x00, UNI_PAIR_RESERVES_SELECTOR)
            // ||UNI_PAIR_RESERVES_SELECTOR|
            if iszero(staticcall(gas(), pool, 0x1c, 0x04, 0x00, 0x40)) { bubbleRevert(ptr) }
            if lt(returndatasize(), 0x40) { revert(0, 0) }
            {
                let r := shl(5, zeroForOne)
                buyReserve := mload(r)
                sellReserve := mload(xor(0x20, r))
            }

            // Update the sell amount in the following cases:
            //   the funds are in the pool already (flagged by sellAmount being 0)
            //   the sell token has a fee (flagged by sellTokenHasFee)
            if or(iszero(sellAmount), sellTokenHasFee) {
                // retrieve the sellToken balance of the pool
                mstore(0x00, ERC20_BALANCEOF_SELECTOR)
                mstore(0x20, and(0xffffffffffffffffffffffffffffffffffffffff, pool))
                // ||ERC20_BALANCEOF_SELECTOR|pool|
                if iszero(staticcall(gas(), sellToken, 0x1c, 0x24, 0x00, 0x20)) { bubbleRevert(ptr) }
                if lt(returndatasize(), 0x20) { revert(0, 0) }
                let bal := mload(0x00)

                // determine real sellAmount by comparing pool's sellToken balance to reserve amount
                if lt(bal, sellReserve) {
                    mstore(0x00, 0x4e487b71) // selector for `Panic(uint256)`
                    mstore(0x20, 0x11) // panic code for arithmetic underflow
                    revert(0x1c, 0x24)
                }
                sellAmount := sub(bal, sellReserve)
            }

            // compute buyAmount based on sellAmount and reserves
            let sellAmountWithFee := mul(sellAmount, sub(10000, feeBps))
            buyAmount := div(mul(sellAmountWithFee, buyReserve), add(sellAmountWithFee, mul(sellReserve, 10000)))
            let swapCalldata := add(ptr, 0x1c)
            // set up swap call selector and empty callback data
            mstore(ptr, UNI_PAIR_SWAP_SELECTOR)
            mstore(add(ptr, 0x80), 0x80) // offset to length of data
            mstore(add(ptr, 0xa0), 0) // length of data

            // set amount0Out and amount1Out
            {
                // If `zeroForOne`, offset is 0x24, else 0x04
                let offset := add(0x04, shl(5, zeroForOne))
                mstore(add(swapCalldata, offset), buyAmount)
                mstore(add(swapCalldata, xor(0x20, offset)), 0)
            }

            mstore(add(swapCalldata, 0x44), and(0xffffffffffffffffffffffffffffffffffffffff, recipient))
            // ...||UNI_PAIR_SWAP_SELECTOR|amount0Out|amount1Out|recipient|data|

            // perform swap at the pool sending bought tokens to the recipient
            if iszero(call(gas(), pool, 0, swapCalldata, 0xa4, 0, 0)) { bubbleRevert(swapCalldata) }

            // revert with the return data from the most recent call
            function bubbleRevert(p) {
                returndatacopy(p, 0, returndatasize())
                revert(p, returndatasize())
            }
        }
        if (buyAmount < minBuyAmount) {
            revert TooMuchSlippage(
                IERC20(zeroForOne ? IUniV2Pair(pool).token1() : IUniV2Pair(pool).token0()), minBuyAmount, buyAmount
            );
        }
    }
}
