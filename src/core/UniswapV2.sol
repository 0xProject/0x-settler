// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {ERC20} from "solmate/src/tokens/ERC20.sol";

interface IUniswapV2 {
    // TODO ShibaSwap, CryptoCom
    enum ProtocolFork {
        UniswapV2,
        SushiSwap
    }
}

abstract contract UniswapV2 {
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

    // Mask of the lower 20 bytes of a bytes32
    uint256 private constant ADDRESS_MASK = 0x000000000000000000000000ffffffffffffffffffffffffffffffffffffffff;
    // Maximum token quantity that can be swapped against the UniswapV2Pair contract
    uint256 private constant MAX_SWAP_AMOUNT = 2 ** 112;
    // Minimum size of an encoded swap path:
    //   sizeof(address(sellToken) | uint8(hopInfo) | address(buyToken))
    // where first bit of `hopInfo` is `sellTokenHasFee` and the rest is `fork`
    uint256 private constant SINGLE_HOP_PATH_SIZE = 20 + 1 + 20;
    // Number of bytes to shift the path by each hop
    uint256 private constant HOP_SHIFT_SIZE = 20 + 1;

    /// @dev TODO
    function sellToUniswapV2(bytes memory encodedPath, uint256 bips) internal {
        // TODO definitely stack too deep, move some stuff into memory and generally optimize
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            let swapCalldata := ptr

            // set up swap call selector and empty callback data
            mstore(ptr, UNI_PAIR_SWAP_CALL_SELECTOR_32)
            mstore(add(ptr, 100), 128) // offset to length of data
            mstore(add(ptr, 132), 0) // length of data

            // 4b selector, 32b amount0Out, 32b amount1Out, 32b to, 64b data
            ptr := add(ptr, 164)

            let fromPool
            let sellAmount

            for {
                let pathLength := mload(encodedPath)
                let path := add(encodedPath, 32)
            } iszero(lt(pathLength, SINGLE_HOP_PATH_SIZE)) {
                pathLength := sub(pathLength, HOP_SHIFT_SIZE)
                path := add(path, HOP_SHIFT_SIZE)
            } {
                let toPool
                let zeroForOne

                // decode hop info
                let buyToken := shr(96, mload(add(path, 21)))
                let sellToken := shr(88, mload(path))
                let sellTokenHasFee := and(0x80, sellToken)
                let fork := and(0x7f, sellToken)
                sellToken := shr(8, sellToken)
                zeroForOne := lt(sellToken, buyToken)

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
                let salt := keccak256(ptr, 40)
                switch fork
                case 0 {
                    // univ2
                    mstore(ptr, UNI_FF_FACTORY_ADDRESS)
                    mstore(add(ptr, 21), salt)
                    mstore(add(ptr, 53), UNI_PAIR_INIT_CODE_HASH)
                }
                case 1 {
                    // sooshie
                    mstore(ptr, SUSHI_FF_FACTORY_ADDRESS)
                    mstore(add(ptr, 21), salt)
                    mstore(add(ptr, 53), SUSHI_PAIR_INIT_CODE_HASH)
                }
                default { revert(0, 0) }
                toPool := and(ADDRESS_MASK, keccak256(ptr, 85))

                // if the next pool is not the initial pool, swap tokens and send to the next pool
                // otherwise, transfer tokens from the settler to the initial pool
                switch iszero(fromPool)
                case 0 {
                    // perform swap at the fromPool sending bought tokens to the toPool
                    mstore(add(swapCalldata, 68), toPool)
                    if iszero(call(gas(), fromPool, 0, swapCalldata, 164, 0, 0)) { bubbleRevert() }
                }
                default {
                    // compute sellAmount based on bips and balance
                    // TODO safety
                    sellAmount := div(mul(bips, balanceOf(ptr, sellToken, address())), 10000)

                    // if we aren't selling anything, abort
                    if eq(sellAmount, 0) { break }

                    // transfer sellAmount of sellToken to the pool
                    mstore(ptr, ERC20_TRANSFER_CALL_SELECTOR_32)
                    mstore(add(ptr, 4), sellToken)
                    mstore(add(ptr, 36), sellAmount)
                    if iszero(call(gas(), sellToken, 0, ptr, 68, 0, 0)) { bubbleRevert() }
                    // TODO check for ERC20 successful return value
                }

                // get toPool reserves
                let sellReserve
                let buyReserve
                mstore(ptr, UNI_PAIR_RESERVES_CALL_SELECTOR_32)
                if iszero(staticcall(gas(), toPool, ptr, 4, ptr, 64)) { bubbleRevert() }
                // TODO check returndatasize
                switch zeroForOne
                case 0 {
                    sellReserve := mload(add(ptr, 32))
                    buyReserve := mload(ptr)
                }
                default {
                    sellReserve := mload(ptr)
                    buyReserve := mload(add(ptr, 20))
                }

                // if the sellToken has a fee on transfer, determine the real sellAmount
                if sellTokenHasFee {
                    // determine real sellAmount by comparing pool's sellToken balance to reserve amount
                    sellAmount := sub(sellReserve, balanceOf(ptr, sellToken, toPool))
                }

                // compute buyAmount based on sellAmount and reserves
                let buyAmount
                {
                    // ensure that the sellAmount is < 2¹¹²
                    if gt(sellAmount, MAX_SWAP_AMOUNT) { revert(0, 0) }
                    // pairs are in the range (0, 2¹¹²) so this shouldn't overflow
                    let sellAmountWithFee := mul(sellAmount, 997)
                    buyAmount := div(mul(sellAmountWithFee, buyReserve), add(sellAmountWithFee, mul(sellReserve, 1000)))
                }

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
            if not(iszero(fromPool)) {
                // perform swap at the fromPool sending bought tokens to settler
                mstore(add(swapCalldata, 68), address())
                if iszero(call(gas(), fromPool, 0, swapCalldata, 164, 0, 0)) { bubbleRevert() }
            }

            // TODO inline
            function balanceOf(p, token, addr) -> bal {
                mstore(p, ERC20_BALANCEOF_CALL_SELECTOR_32)
                mstore(add(p, 4), addr)
                if iszero(call(gas(), token, 0, p, 36, p, 32)) { bubbleRevert() }
                // TODO check returndatasize
                bal := mload(p)
            }

            // revert with the return data from the most recent call
            function bubbleRevert() {
                returndatacopy(0, 0, returndatasize())
                revert(0, returndatasize())
            }
        }
    }
}
