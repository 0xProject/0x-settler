// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {Ternary} from "../utils/Ternary.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {Panic} from "../utils/Panic.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {AddressDerivation} from "../utils/AddressDerivation.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";

import {revertTooMuchSlippage} from "./SettlerErrors.sol";

interface IUniswapV3Pool {
    /// @notice Swap token0 for token1, or token1 for token0
    /// @dev The caller of this method receives a callback in the form of IUniswapV3SwapCallback#uniswapV3SwapCallback
    /// @param recipient The address to receive the output of the swap
    /// @param zeroForOne The direction of the swap, true for token0 to token1, false for token1 to token0
    /// @param amountSpecified The amount of the swap, which implicitly configures the swap as exact input (positive),
    /// or exact output (negative)
    /// @param sqrtPriceLimitX96 The Q64.96 sqrt price limit. If zero for one, the price cannot be less than this
    /// value after the swap. If one for zero, the price cannot be greater than this value after the swap
    /// @param data Any data to be passed through to the callback
    /// @return amount0 The delta of the balance of token0 of the pool, exact when negative, minimum when positive
    /// @return amount1 The delta of the balance of token1 of the pool, exact when negative, minimum when positive
    function swap(
        address recipient,
        bool zeroForOne,
        int256 amountSpecified,
        uint160 sqrtPriceLimitX96,
        bytes calldata data
    ) external returns (int256 amount0, int256 amount1);
}

abstract contract UniswapV3Fork is SettlerAbstract {
    using Ternary for bool;
    using UnsafeMath for uint256;
    using UnsafeMath for int256;
    using SafeTransferLib for IERC20;

    /// @dev Minimum size of an encoded swap path:
    ///      sizeof(address(inputToken) | uint8(forkId) | uint24(poolId) | uint160(sqrtPriceLimitX96) | address(outputToken))
    uint256 private constant SINGLE_HOP_PATH_SIZE = 0x40;
    /// @dev How many bytes to skip ahead in an encoded path to start at the next hop:
    ///      sizeof(address(inputToken) | uint8(forkId) | uint24(poolId) | uint160(sqrtPriceLimitX96))
    uint256 private constant PATH_SKIP_HOP_SIZE = 0x2c;
    /// @dev The size of the swap callback prefix data before the Permit2 data.
    uint256 private constant SWAP_CALLBACK_PREFIX_DATA_SIZE = 0x28;
    /// @dev The offset from the pointer to the length of the swap callback prefix data to the start of the Permit2 data.
    uint256 private constant SWAP_CALLBACK_PERMIT2DATA_OFFSET = 0x48;
    uint256 private constant PERMIT_DATA_SIZE = 0x60;
    uint256 private constant ISFORWARDED_DATA_SIZE = 0x01;
    /// @dev Mask of lower 3 bytes.
    uint256 private constant UINT24_MASK = 0xffffff;

    /// @dev Sell a token for another token directly against uniswap v3.
    /// @param encodedPath Uniswap-encoded path.
    /// @param bps proportion of current balance of the first token in the path to sell.
    /// @param minBuyAmount Minimum amount of the last token in the path to buy.
    /// @param recipient The recipient of the bought tokens.
    /// @return buyAmount Amount of the last token in the path bought.
    function sellToUniswapV3(address recipient, uint256 bps, bytes memory encodedPath, uint256 minBuyAmount)
        internal
        returns (uint256 buyAmount)
    {
        buyAmount = _uniV3ForkSwap(
            recipient,
            encodedPath,
            // We don't care about phantom overflow here because reserves are
            // limited to 128 bits. Any token balance that would overflow here
            // would also break UniV3.
            (IERC20(address(bytes20(encodedPath))).fastBalanceOf(address(this)) * bps).unsafeDiv(BASIS),
            minBuyAmount,
            address(this), // payer
            new bytes(SWAP_CALLBACK_PREFIX_DATA_SIZE)
        );
    }

    /// @dev Sell a token for another token directly against uniswap v3. Payment is using a Permit2 signature (or AllowanceHolder).
    /// @param encodedPath Uniswap-encoded path.
    /// @param minBuyAmount Minimum amount of the last token in the path to buy.
    /// @param recipient The recipient of the bought tokens.
    /// @param permit The PermitTransferFrom allowing this contract to spend the taker's tokens
    /// @param sig The taker's signature for Permit2
    /// @return buyAmount Amount of the last token in the path bought.
    function sellToUniswapV3VIP(
        address recipient,
        bytes memory encodedPath,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig,
        uint256 minBuyAmount
    ) internal returns (uint256 buyAmount) {
        bytes memory swapCallbackData =
            new bytes(SWAP_CALLBACK_PREFIX_DATA_SIZE + PERMIT_DATA_SIZE + ISFORWARDED_DATA_SIZE + sig.length);
        _encodePermit2Data(swapCallbackData, permit, sig, _isForwarded());

        buyAmount = _uniV3ForkSwap(
            recipient,
            encodedPath,
            _permitToSellAmount(permit),
            minBuyAmount,
            address(0), // payer
            swapCallbackData
        );
    }

    // Executes successive swaps along an encoded uniswap path.
    function _uniV3ForkSwap(
        address recipient,
        bytes memory encodedPath,
        uint256 sellAmount,
        uint256 minBuyAmount,
        address payer,
        bytes memory swapCallbackData
    ) internal returns (uint256 buyAmount) {
        if (sellAmount > uint256(type(int256).max)) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }

        IERC20 outputToken;
        while (true) {
            bool isPathMultiHop = _isPathMultiHop(encodedPath);
            bool zeroForOne;
            IUniswapV3Pool pool;
            uint160 sqrtPriceLimitX96;
            uint32 callbackSelector;
            {
                IERC20 token0;
                uint8 forkId;
                uint24 poolId;
                IERC20 token1;
                (token0, forkId, poolId, sqrtPriceLimitX96, token1) = _decodeFirstPoolInfoFromPath(encodedPath);

                IERC20 sellToken = token0;
                outputToken = token1;
                (token0, token1) = (zeroForOne = token0 < token1).maybeSwap(token1, token0);
                address factory;
                bytes32 initHash;
                (factory, initHash, callbackSelector) = _uniV3ForkInfo(forkId);
                pool = _toPool(forkId, factory, initHash, token0, token1, poolId);
                _updateSwapCallbackData(swapCallbackData, sellToken, payer);
            }

            // Intermediate tokens go to this contract. Final tokens go to `recipient`.
            address to = isPathMultiHop.ternary(address(this), recipient);

            uint256 freeMemPtr;
            bytes memory data;
            assembly ("memory-safe") {
                freeMemPtr := mload(0x40)
                data := freeMemPtr

                // encode the call to pool.swap
                let callbackLen := mload(swapCallbackData)
                mcopy(add(0xc4, data), swapCallbackData, add(0x20, callbackLen))
                mstore(add(0xa4, data), 0xa0)
                mstore(add(0x84, data), and(0xffffffffffffffffffffffffffffffffffffffff, sqrtPriceLimitX96))
                mstore(add(0x64, data), sellAmount)
                mstore(add(0x44, data), zeroForOne)
                mstore(add(0x24, data), to)
                mstore(add(0x10, data), 0x128acb08000000000000000000000000) // selector for `swap(address,bool,int256,uint160,bytes)` with `to`'s padding

                // set data.length
                mstore(data, add(0xc4, callbackLen))

                // advance the free memory pointer (we'll put it back later)
                mstore(0x40, add(add(0xe4, callbackLen), data))
            }

            (int256 amount0, int256 amount1) = abi.decode(
                _setOperatorAndCall(address(pool), data, callbackSelector, _uniV3ForkCallback), (int256, int256)
            );

            assembly ("memory-safe") {
                // release the memory that we allocated above
                mstore(0x40, freeMemPtr)
            }

            {
                int256 _buyAmount = zeroForOne.ternary(amount1, amount0).unsafeNeg();
                if (_buyAmount < 0) {
                    Panic.panic(Panic.ARITHMETIC_OVERFLOW);
                }
                buyAmount = uint256(_buyAmount);
            }
            if (!isPathMultiHop) {
                // Done.
                break;
            }
            // Continue with next hop.
            payer = address(this); // Subsequent hops are paid for by us.
            sellAmount = buyAmount;
            // Skip to next hop along path.
            encodedPath = _shiftHopFromPathInPlace(encodedPath);
            assembly ("memory-safe") {
                mstore(swapCallbackData, SWAP_CALLBACK_PREFIX_DATA_SIZE)
            }
        }
        if (buyAmount < minBuyAmount) {
            revertTooMuchSlippage(outputToken, minBuyAmount, buyAmount);
        }
    }

    // Return whether or not an encoded uniswap path contains more than one hop.
    function _isPathMultiHop(bytes memory encodedPath) private pure returns (bool) {
        return encodedPath.length > SINGLE_HOP_PATH_SIZE;
    }

    function _decodeFirstPoolInfoFromPath(bytes memory encodedPath)
        private
        pure
        returns (IERC20 inputToken, uint8 forkId, uint24 poolId, uint160 sqrtPriceLimitX96, IERC20 outputToken)
    {
        if (encodedPath.length < SINGLE_HOP_PATH_SIZE) {
            Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
        }
        assembly ("memory-safe") {
            // Solidity cleans dirty bits automatically
            inputToken := mload(add(0x14, encodedPath))
            forkId := mload(add(0x15, encodedPath))
            poolId := mload(add(0x18, encodedPath))
            sqrtPriceLimitX96 := mload(add(0x2c, encodedPath))
            outputToken := mload(add(SINGLE_HOP_PATH_SIZE, encodedPath))
        }
    }

    // Skip past the first hop of an encoded uniswap path in-place.
    function _shiftHopFromPathInPlace(bytes memory encodedPath) private pure returns (bytes memory) {
        if (encodedPath.length < PATH_SKIP_HOP_SIZE) {
            Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
        }
        assembly ("memory-safe") {
            let length := sub(mload(encodedPath), PATH_SKIP_HOP_SIZE)
            encodedPath := add(encodedPath, PATH_SKIP_HOP_SIZE)
            mstore(encodedPath, length)
        }
        return encodedPath;
    }

    function _encodePermit2Data(
        bytes memory swapCallbackData,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig,
        bool isForwarded
    ) private pure {
        assembly ("memory-safe") {
            mstore(add(SWAP_CALLBACK_PERMIT2DATA_OFFSET, swapCallbackData), mload(add(0x20, mload(permit))))
            mcopy(add(add(SWAP_CALLBACK_PERMIT2DATA_OFFSET, 0x20), swapCallbackData), add(0x20, permit), 0x40)
            mstore8(add(add(SWAP_CALLBACK_PERMIT2DATA_OFFSET, PERMIT_DATA_SIZE), swapCallbackData), isForwarded)
            mcopy(
                add(
                    add(add(SWAP_CALLBACK_PERMIT2DATA_OFFSET, PERMIT_DATA_SIZE), ISFORWARDED_DATA_SIZE),
                    swapCallbackData
                ),
                add(0x20, sig),
                mload(sig)
            )
        }
    }

    // Update `swapCallbackData` in place with new values.
    function _updateSwapCallbackData(bytes memory swapCallbackData, IERC20 sellToken, address payer) private pure {
        assembly ("memory-safe") {
            let length := mload(swapCallbackData)
            mstore(add(0x28, swapCallbackData), sellToken)
            mstore(add(0x14, swapCallbackData), payer)
            mstore(swapCallbackData, length)
        }
    }

    function _isEraVmUniV3Fork(uint8) internal pure virtual returns (bool) {
        return false;
    }

    // Compute the pool address given two tokens and a poolId.
    function _toPool(uint8 forkId, address factory, bytes32 initHash, IERC20 token0, IERC20 token1, uint24 poolId)
        private
        pure
        returns (IUniswapV3Pool)
    {
        // address(keccak256(abi.encodePacked(
        //     hex"ff",
        //     factory,
        //     keccak256(abi.encode(token0, token1, poolId)),
        //     initHash
        // )))
        bytes32 salt;
        assembly ("memory-safe") {
            poolId := and(UINT24_MASK, poolId)
            let ptr := mload(0x40)
            mstore(0x40, poolId)
            mstore(0x20, token1)
            mstore(0x00, 0x00)
            mstore(0x0c, shl(0x60, token0))
            salt := keccak256(0x00, sub(0x60, shl(0x05, iszero(poolId))))
            mstore(0x40, ptr)
        }
        if (_isEraVmUniV3Fork(forkId)) {
            return IUniswapV3Pool(
                AddressDerivation.deriveDeterministicContractEraVm(
                    factory, salt, initHash, 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470
                )
            );
        } else {
            return IUniswapV3Pool(AddressDerivation.deriveDeterministicContract(factory, salt, initHash));
        }
    }

    function _uniV3ForkInfo(uint8 forkId) internal view virtual returns (address, bytes32, uint32);

    function _uniV3ForkCallback(bytes calldata data) private returns (bytes memory) {
        require(data.length >= 0x80);
        int256 amount0Delta;
        int256 amount1Delta;
        assembly ("memory-safe") {
            amount0Delta := calldataload(data.offset)
            amount1Delta := calldataload(add(0x20, data.offset))
            data.offset := add(data.offset, calldataload(add(0x40, data.offset)))
            data.length := calldataload(data.offset)
            data.offset := add(0x20, data.offset)
        }
        uniswapV3SwapCallback(amount0Delta, amount1Delta, data);
        return new bytes(0);
    }

    /// @dev The UniswapV3 pool swap callback which pays the funds requested
    ///      by the caller/pool to the pool. Can only be called by a valid
    ///      UniswapV3 pool.
    /// @param amount0Delta Token0 amount owed.
    /// @param amount1Delta Token1 amount owed.
    /// @param data Arbitrary data forwarded from swap() caller. A packed encoding of: payer, sellToken, (optionally: permit[0x20:], isForwarded, sig)
    function uniswapV3SwapCallback(int256 amount0Delta, int256 amount1Delta, bytes calldata data) private {
        address payer;
        assembly ("memory-safe") {
            payer := shr(0x60, calldataload(data.offset))
            data.length := sub(data.length, 0x14)
            data.offset := add(0x14, data.offset)
            // We don't check for underflow/array-out-of-bounds here because the trusted inithash
            // ensures that `data` was passed unmodified from `_updateSwapCallbackData`. Therefore,
            // it is at least 40 bytes long.
        }
        uint256 sellAmount = (amount0Delta > 0).ternary(uint256(amount0Delta), uint256(amount1Delta));
        _pay(payer, sellAmount, data);
    }

    function _pay(address payer, uint256 amount, bytes calldata permit2Data) private {
        if (payer == address(this)) {
            IERC20 token;
            assembly ("memory-safe") {
                token := shr(0x60, calldataload(permit2Data.offset))
            }
            token.safeTransfer(msg.sender, amount);
        } else {
            assert(payer == address(0));
            ISignatureTransfer.PermitTransferFrom calldata permit;
            bool isForwarded;
            bytes calldata sig;
            assembly ("memory-safe") {
                // this is super dirty, but it works because although `permit` is aliasing in the
                // middle of `payer`, because `payer` is all zeroes, it's treated as padding for the
                // first word of `permit`, which is the sell token
                permit := sub(permit2Data.offset, 0x0c)
                isForwarded := and(0x01, calldataload(add(0x55, permit2Data.offset)))
                sig.offset := add(0x75, permit2Data.offset)
                sig.length := sub(permit2Data.length, 0x75)
            }
            ISignatureTransfer.SignatureTransferDetails memory transferDetails =
                ISignatureTransfer.SignatureTransferDetails({to: msg.sender, requestedAmount: amount});
            _transferFrom(permit, transferDetails, sig, isForwarded);
        }
    }
}
