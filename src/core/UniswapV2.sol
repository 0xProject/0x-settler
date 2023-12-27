// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {ERC20} from "solmate/src/tokens/ERC20.sol";
import {FullMath} from "../utils/FullMath.sol";
import {Panic} from "../utils/Panic.sol";
import {VIPBase} from "./VIPBase.sol";

abstract contract UniswapV2 is VIPBase {
    using FullMath for uint256;

    // UniswapV2 Factory contract address prepended with '0xff' and left-aligned
    bytes32 private constant UNI_FF_FACTORY_ADDRESS = 0xFF5C69bEe701ef814a2B6a3EDD4B1652CB9cc5aA6f0000000000000000000000;
    // UniswapV2 pool init code hash
    bytes32 private constant UNI_PAIR_INIT_CODE_HASH =
        0x96e8ac4277198ff8b6f785478aa9a39f403cb768dd02cbee326c3e7da348845f;

    // SushiSwap Factory contract address prepended with '0xff' and left-aligned
    bytes32 private constant SUSHI_FF_FACTORY_ADDRESS =
        0xFFC0AEe478e3658e2610c5F7A4A2E1777cE9e4f2Ac0000000000000000000000;
    // SushiSwap pool init code hash
    bytes32 private constant SUSHI_PAIR_INIT_CODE_HASH =
        0xe18a34eb0e04b04f7a0ac29a6e80748dca96319b42c54d679cb821dca90c6303;

    // bytes4(keccak256("getReserves()"))
    uint256 private constant UNI_PAIR_RESERVES_CALL_SELECTOR_32 =
        0x0902f1ac00000000000000000000000000000000000000000000000000000000;
    // bytes4(keccak256("swap(uint256,uint256,address,bytes)"))
    uint256 private constant UNI_PAIR_SWAP_CALL_SELECTOR_32 =
        0x022c0d9f00000000000000000000000000000000000000000000000000000000;
    // bytes4(keccak256("transfer(address,uint256)"))
    uint256 private constant ERC20_TRANSFER_CALL_SELECTOR_32 =
        0xa9059cbb00000000000000000000000000000000000000000000000000000000;
    // bytes4(keccak256("balanceOf(address)"))
    uint256 private constant ERC20_BALANCEOF_CALL_SELECTOR_32 =
        0x70a0823100000000000000000000000000000000000000000000000000000000;

    // Minimum size of an encoded swap path:
    //   sizeof(address(sellToken) | uint8(hopInfo) | address(buyToken))
    // where first bit of `hopInfo` is `sellTokenHasFee` and the rest is `fork`
    uint256 private constant SINGLE_HOP_PATH_SIZE = 20 + 1 + 20;
    // Number of bytes to shift the path by each hop
    uint256 private constant HOP_SHIFT_SIZE = 20 + 1;

    /// @dev Sell a token for another token using UniswapV2.
    /// @param encodedPath Custom encoded path of the swap.
    /// @param bips Bips to sell of settler's balance of the initial token in the path.
    function sellToUniswapV2(address recipient, bytes memory encodedPath, uint256 bips, uint256 minBuyAmount)
        internal
    {
        if (encodedPath.length < SINGLE_HOP_PATH_SIZE) {
            Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
        }

        uint256 sellAmount = ERC20(address(bytes20(encodedPath))).balanceOf(address(this)).mulDiv(bips, 10_000);
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            let swapCalldata := ptr
            let fromPool

            // set up swap call selector and empty callback data
            mstore(ptr, UNI_PAIR_SWAP_CALL_SELECTOR_32)
            mstore(add(ptr, 100), 128) // offset to length of data
            mstore(add(ptr, 132), 0) // length of data

            // 4b selector, 32b amount0Out, 32b amount1Out, 32b to, 64b data
            ptr := add(ptr, 164)

            for {
                let pathLength := mload(encodedPath)
                let path := add(encodedPath, 32)
            } iszero(lt(pathLength, SINGLE_HOP_PATH_SIZE)) {
                pathLength := sub(pathLength, HOP_SHIFT_SIZE)
                path := add(path, HOP_SHIFT_SIZE)
            } {
                // decode hop info
                let buyToken := shr(96, mload(add(path, 21)))
                let sellToken := shr(88, mload(path))
                let sellTokenHasFee := and(0x80, sellToken)
                let fork := and(0x7f, sellToken)
                sellToken := shr(8, sellToken)
                let zeroForOne := lt(sellToken, buyToken)

                // compute the pool address
                // address(keccak256(abi.encodePacked(
                //     hex"ff",
                //     UNI_FACTORY_ADDRESS,
                //     keccak256(abi.encodePacked(token0, token1)),
                //     UNI_POOL_INIT_CODE_HASH
                // )))
                switch zeroForOne
                case 0 {
                    mstore(add(ptr, 20), sellToken)
                    mstore(ptr, buyToken)
                }
                default {
                    mstore(add(ptr, 20), buyToken)
                    mstore(ptr, sellToken)
                }
                let salt := keccak256(add(ptr, 12), 40)
                switch fork
                case 0 {
                    // univ2
                    mstore(ptr, UNI_FF_FACTORY_ADDRESS)
                    mstore(add(ptr, 21), salt)
                    mstore(add(ptr, 53), UNI_PAIR_INIT_CODE_HASH)
                }
                case 1 {
                    // sushi
                    mstore(ptr, SUSHI_FF_FACTORY_ADDRESS)
                    mstore(add(ptr, 21), salt)
                    mstore(add(ptr, 53), SUSHI_PAIR_INIT_CODE_HASH)
                }
                default { revert(0, 0) }
                let toPool := keccak256(ptr, 85)

                // if the next pool is the initial pool, transfer tokens from the settler to the initial pool
                // otherwise, swap tokens and send to the next pool
                switch fromPool
                case 0 {
                    // transfer sellAmount of sellToken to the pool
                    mstore(ptr, ERC20_TRANSFER_CALL_SELECTOR_32)
                    mstore(add(ptr, 4), toPool)
                    mstore(add(ptr, 36), sellAmount)
                    if iszero(call(gas(), sellToken, 0, ptr, 68, ptr, 32)) { bubbleRevert() }
                    if iszero(or(iszero(returndatasize()), and(iszero(lt(returndatasize(), 32)), eq(mload(ptr), 1)))) {
                        revert(0, 0)
                    }
                }
                default {
                    // perform swap at the fromPool sending bought tokens to the toPool
                    mstore(add(swapCalldata, 68), toPool)
                    if iszero(call(gas(), fromPool, 0, swapCalldata, 164, 0, 0)) { bubbleRevert() }
                }

                // get toPool reserves
                let sellReserve
                let buyReserve
                mstore(ptr, UNI_PAIR_RESERVES_CALL_SELECTOR_32)
                if iszero(staticcall(gas(), toPool, ptr, 4, ptr, 64)) { bubbleRevert() }
                if lt(returndatasize(), 64) { revert(0, 0) }
                switch zeroForOne
                case 0 {
                    sellReserve := mload(add(ptr, 32))
                    buyReserve := mload(ptr)
                }
                default {
                    sellReserve := mload(ptr)
                    buyReserve := mload(add(ptr, 32))
                }

                // if the sellToken has a fee on transfer, determine the real sellAmount
                if sellTokenHasFee {
                    // retrieve the sellToken balance of the pool
                    mstore(ptr, ERC20_BALANCEOF_CALL_SELECTOR_32)
                    mstore(add(ptr, 4), toPool)
                    if iszero(staticcall(gas(), sellToken, ptr, 36, ptr, 32)) { bubbleRevert() }
                    if lt(returndatasize(), 32) { revert(0, 0) }
                    let bal := mload(ptr)

                    // determine real sellAmount by comparing pool's sellToken balance to reserve amount
                    if lt(bal, sellReserve) {
                        mstore(0x00, 0x4e487b71) // selector for `Panic(uint256)`
                        mstore(0x20, 0x11) // panic code for arithmetic underflow
                        revert(0x1c, 0x24)
                    }
                    sellAmount := sub(bal, sellReserve)
                }

                // compute buyAmount based on sellAmount and reserves
                let sellAmountWithFee := mul(sellAmount, 997)
                let buyAmount := div(mul(sellAmountWithFee, buyReserve), add(sellAmountWithFee, mul(sellReserve, 1000)))

                // set amount0Out and amount1Out
                switch zeroForOne
                case 0 {
                    mstore(add(swapCalldata, 4), buyAmount)
                    mstore(add(swapCalldata, 36), 0)
                }
                default {
                    mstore(add(swapCalldata, 4), 0)
                    mstore(add(swapCalldata, 36), buyAmount)
                }

                // shift pools and amounts for next iteration
                fromPool := toPool
                sellAmount := buyAmount
            }

            // final swap
            if fromPool {
                // perform swap at the fromPool sending bought tokens to settler
                mstore(add(swapCalldata, 68), and(0xffffffffffffffffffffffffffffffffffffffff, recipient))
                if iszero(call(gas(), fromPool, 0, swapCalldata, 164, 0, 0)) { bubbleRevert() }
            }

            // revert with the return data from the most recent call
            function bubbleRevert() {
                let p := mload(0x40)
                returndatacopy(p, 0, returndatasize())
                revert(p, returndatasize())
            }
        }
        // sellAmount is the amount sent from the final hop
        if (sellAmount < minBuyAmount) {
            address buyToken;
            assembly ("memory-safe") {
                buyToken := mload(add(encodedPath, mload(encodedPath)))
            }
            revert TooMuchSlippage(buyToken, minBuyAmount, sellAmount);
        }
    }
}
