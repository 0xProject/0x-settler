// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";
import {AddressDerivation} from "../utils/AddressDerivation.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";

import {TooMuchSlippage} from "./SettlerErrors.sol";

// Maverick AMM V2 is not open-source. The source code was disclosed to the
// developers of 0x Settler confidentially and recompiled privately. The
// deployed bytecode inithash matches the privately recompiled inithash.
bytes32 constant maverickV2InitHash = 0xbb7b783eb4b8ca46925c5384a6b9919df57cb83da8f76e37291f58d0dd5c439a;

// https://docs.mav.xyz/technical-reference/contract-addresses/v2-contract-addresses
// For chains: mainnet, base, bnb, arbitrum, scroll
address constant maverickV2Factory = 0x0A7e848Aca42d879EF06507Fca0E7b33A0a63c1e;

interface IMaverickV2Pool {
    /**
     * @notice Parameters for swap.
     * @param amount Amount of the token that is either the input if exactOutput is false
     * or the output if exactOutput is true.
     * @param tokenAIn Boolean indicating whether tokenA is the input.
     * @param exactOutput Boolean indicating whether the amount specified is
     * the exact output amount (true).
     * @param tickLimit The furthest tick a swap will execute in. If no limit
     * is desired, value should be set to type(int32).max for a tokenAIn swap
     * and type(int32).min for a swap where tokenB is the input.
     */
    struct SwapParams {
        uint256 amount;
        bool tokenAIn;
        bool exactOutput;
        int32 tickLimit;
    }

    /**
     * @notice Swap tokenA/tokenB assets in the pool.  The swap user has two
     * options for funding their swap.
     * - The user can push the input token amount to the pool before calling
     * the swap function. In order to avoid having the pool call the callback,
     * the user should pass a zero-length `data` bytes object with the swap
     * call.
     * - The user can send the input token amount to the pool when the pool
     * calls the `maverickV2SwapCallback` function on the calling contract.
     * That callback has input parameters that specify the token address of the
     * input token, the input and output amounts, and the bytes data sent to
     * the swap function.
     * @dev  If the users elects to do a callback-based swap, the output
     * assets will be sent before the callback is called, allowing the user to
     * execute flash swaps.  However, the pool does have reentrancy protection,
     * so a swapper will not be able to interact with the same pool again
     * while they are in the callback function.
     * @param recipient The address to receive the output tokens.
     * @param params Parameters containing the details of the swap
     * @param data Bytes information that gets passed to the callback.
     */
    function swap(address recipient, SwapParams calldata params, bytes calldata data)
        external
        returns (uint256 amountIn, uint256 amountOut);
}

interface IMaverickV2SwapCallback {
    function maverickV2SwapCallback(IERC20 tokenIn, uint256 amountIn, uint256 amountOut, bytes calldata data)
        external;
}

abstract contract MaverickV2 is SettlerAbstract {
    using UnsafeMath for uint256;
    using SafeTransferLib for IERC20;

    function _pool(
        uint256 feeAIn,
        uint256 feeBIn,
        uint256 tickSpacing,
        uint256 lookback,
        IERC20 tokenA,
        IERC20 tokenB,
        uint8 kinds
    ) private pure returns (IMaverickV2Pool) {
        bytes32 salt = keccak256(abi.encode(feeAIn, feeBIn, tickSpacing, lookback, tokenA, tokenB, kinds, address(0)));
        return
            IMaverickV2Pool(AddressDerivation.deriveDeterministicContract(maverickV2Factory, salt, maverickV2InitHash));
    }

    function _unpackPoolId(bytes memory poolId, IERC20 sellToken)
        private
        pure
        returns (
            bool tokenAIn,
            IERC20 buyToken,
            uint64 feeAIn,
            uint64 feeBIn,
            uint16 tickSpacing,
            uint32 lookback,
            IERC20 tokenA,
            IERC20 tokenB,
            uint8 kinds
        )
    {
        assembly ("memory-safe") {
            tokenAIn := mload(add(0x01, poolId))
            feeAIn := mload(add(0x09, poolId))
            feeBIn := mload(add(0x11, poolId))
            tickSpacing := mload(add(0x13, poolId))
            lookback := mload(add(0x17, poolId))
            buyToken := mload(add(0x2b, poolId))
            kinds := mload(add(0x2c, poolId))
        }
        (tokenA, tokenB) = tokenAIn ? (sellToken, buyToken) : (tokenB, buyToken);
    }

    function _encodeSwapCallback(ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig)
        internal
        view
        returns (bytes memory result)
    {
        bool isForwarded = _isForwarded();
        assembly ("memory-safe") {
            result := mload(0x40)
            mcopy(add(0x20, result), mload(permit), 0x40)
            mcopy(add(0x60, result), add(0x20, permit), 0x40)
            mstore8(add(0xa0, result), isForwarded)
            let sigLength := mload(sig)
            mcopy(add(0xa1, result), add(0x20, sig), sigLength)
            mstore(result, add(0x81, sigLength))
            mstore(0x40, add(sigLength, add(0xa1, result)))
        }
    }

    function sellToMaverickV2VIP(
        address recipient,
        bytes memory poolId,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig,
        uint256 minBuyAmount
    ) internal returns (uint256 buyAmount) {
        bytes memory swapCallbackData = _encodeSwapCallback(permit, sig);
        IERC20 sellToken = IERC20(permit.permitted.token);
        (
            bool tokenAIn,
            IERC20 buyToken,
            uint64 feeAIn,
            uint64 feeBIn,
            uint16 tickSpacing,
            uint32 lookback,
            IERC20 tokenA,
            IERC20 tokenB,
            uint8 kinds
        ) = _unpackPoolId(poolId, sellToken);
        IMaverickV2Pool pool = _pool(feeAIn, feeBIn, tickSpacing, lookback, tokenA, tokenB, kinds);
        (, buyAmount) = abi.decode(
            _setOperatorAndCall(
                address(pool),
                abi.encodeCall(
                    pool.swap,
                    (
                        recipient,
                        IMaverickV2Pool.SwapParams({
                            amount: permit.permitted.amount,
                            tokenAIn: tokenAIn,
                            exactOutput: false,
                            tickLimit: tokenAIn ? type(int32).max : type(int32).min
                        }),
                        swapCallbackData
                    )
                ),
                uint32(IMaverickV2SwapCallback.maverickV2SwapCallback.selector),
                _maverickV2Callback
            ),
            (uint256, uint256)
        );
        if (buyAmount < minBuyAmount) {
            revert TooMuchSlippage(buyToken, minBuyAmount, buyAmount);
        }
    }

    function sellToMaverickV2(
        address recipient,
        IERC20 sellToken,
        uint256 bps,
        bytes memory poolId,
        uint256 minBuyAmount
    ) internal returns (uint256 buyAmount) {
        (
            bool tokenAIn,
            IERC20 buyToken,
            uint64 feeAIn,
            uint64 feeBIn,
            uint16 tickSpacing,
            uint32 lookback,
            IERC20 tokenA,
            IERC20 tokenB,
            uint8 kinds
        ) = _unpackPoolId(poolId, sellToken);
        // We don't care about phantom overflow here because reserves are
        // limited to 128 bits. Any token balance that would overflow here
        // would also break MaverickV2.
        uint256 sellAmount = (sellToken.balanceOf(address(this)) * bps).unsafeDiv(10_000);
        IMaverickV2Pool pool = _pool(feeAIn, feeBIn, tickSpacing, lookback, tokenA, tokenB, kinds);
        sellToken.safeTransfer(address(pool), sellAmount);
        (, buyAmount) = pool.swap(
            recipient,
            IMaverickV2Pool.SwapParams({
                amount: sellAmount,
                tokenAIn: tokenAIn,
                exactOutput: false,
                tickLimit: tokenAIn ? type(int32).max : type(int32).min
            }),
            new bytes(0)
        );
        if (buyAmount < minBuyAmount) {
            revert TooMuchSlippage(buyToken, minBuyAmount, buyAmount);
        }
    }

    function _maverickV2Callback(bytes calldata data) private returns (bytes memory) {
        require(data.length >= 0xa0);
        IERC20 tokenIn;
        uint256 amountIn;
        assembly ("memory-safe") {
            // we don't bother checking for dirty bits because we trust the
            // initcode (by its hash) to produce well-behaved bytecode that
            // produces strict ABI-encoded calldata
            tokenIn := calldataload(data.offset)
            amountIn := calldataload(add(0x20, data.offset))
            // likewise, we don't bother to perform the indirection to find the
            // nested data. we just index directly to it because we know that
            // the pool follows strict ABI encoding
            data.offset := add(0x80, data.offset)
            data.length := calldataload(data.offset)
            data.offset := add(0x20, data.offset)
        }
        maverickV2SwapCallback(
            tokenIn,
            amountIn,
            // forgefmt: disable-next-line
            0 /* we didn't bother loading `amountOut` because we don't use it */,
            data
        );
        return new bytes(0);
    }

    // forgefmt: disable-next-line
    function maverickV2SwapCallback(IERC20 tokenIn, uint256 amountIn, uint256 /* amountOut */, bytes calldata data)
        private
    {
        ISignatureTransfer.PermitTransferFrom calldata permit;
        bool isForwarded;
        assembly ("memory-safe") {
            permit := data.offset
            isForwarded := and(0x01, calldataload(add(0x61, data.offset)))
            data.offset := add(0x81, data.offset)
            data.length := sub(data.length, 0x81)
        }
        _transferFrom(
            permit,
            ISignatureTransfer.SignatureTransferDetails({to: msg.sender, requestedAmount: amountIn}),
            data,
            isForwarded
        );
    }
}
