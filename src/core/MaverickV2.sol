// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";
import {AddressDerivation} from "../utils/AddressDerivation.sol";
import {Panic} from "../utils/Panic.sol";

import {TooMuchSlippage} from "./SettlerErrors.sol";

// Maverick AMM V2 is not open-source. The source code was disclosed to the
// developers of 0x Settler confidentially and recompiled privately. The
// deployed bytecode inithash matches the privately recompiled inithash.
bytes32 maverickV2InitHash = 0xbb7b783eb4b8ca46925c5384a6b9919df57cb83da8f76e37291f58d0dd5c439a;

// https://docs.mav.xyz/technical-reference/contract-addresses/v2-contract-addresses
// For chains: mainnet, base, bnb, arbitrum, scroll
address maverickV2Factory = 0x0A7e848Aca42d879EF06507Fca0E7b33A0a63c1e;

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
    // fees are with basis 10**18 (60 bits max)
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

    function _encodeSwapCallback(
        bytes memory swapCallbackData,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig
    ) internal pure {
        if (swapCallbackData.length < 0x95 + sig.length) {
            Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
        }
        bool isForwarded = _isForwarded();
        assembly ("memory-safe") {
            mstore(add(0x14, swapCallbackData), 0x00)
            mcopy(add(0x34, swapCallbackData), mload(permit), 0x40)
            mcopy(add(0x74, swapCallbackData), add(0x20, permit), 0x40)
            mstore8(add(0xb4, swapCallbackData), isForwarded)
            let sigLength := mload(sig)
            mcopy(add(0xb5, swapCallbackData), add(0x20, sig), sigLength)
            mstore(swapCallbackData, add(0x95, sigLength))
        }
    }

    function _encodeSwapCallback(bytes memory swapCallbackData) internal pure {
        if (swapCallbackData.length < 0x14) {
            Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
        }
        assembly ("memory-safe") {
            mstore(add(0x14, swapCallbackData), address())
            mstore(swapCallbackData, 0x14)
        }
    }

    function sellToMaverickV2VIP(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig,
        uint256 minBuyAmount
    ) internal returns (uint256 buyAmount) {
        IERC20 sellToken = IERC20(permit.permitted.token);
        bytes memory swapCallbackData = new bytes(0x95 + sig.length);
        _encodeSwapCallback(swapCallbackData, permit, sig);
        (IERC20 tokenA, IERC20 tokenB) = tokenAIn ? (sellToken, buyToken) : (buyToken, sellToken);
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
        address sellToken,
        uint256 bps
        uint256 minBuyAmount
    ) internal returns (uint256 buyAmount) {
        uint256 sellAmount = (sellToken.balanceOf(address(this)) * bps).unsafeDiv(10_000);
        (IERC20 tokenA, IERC20 tokenB) = tokenAIn ? (sellToken, buyToken) : (buyToken, sellToken);
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
            // initcode (by its hash) to produce well-behaved bytecode
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
        address payer = address(uint160(bytes20(data)));
        data = data[0x14:];
        _pay(payer, sellAmount, data);
    }

    function _pay(IERC20 tokenIn, uint256 amountIn, address payer, bytes calldata permit2Data) private {
        if (payer == address(this)) {
            tokenIn.safeTransfer(msg.sender, amountIn);
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
                isForwarded := calldataload(add(0x55, permit2Data.offset))
                sig.offset := add(0x75, permit2Data.offset)
                sig.length := sub(permit2Data.length, 0x75)
            }
            _transferFrom(
                permit,
                ISignatureTransfer.SignatureTransferDetails({to: msg.sender, requestedAmount: amount}),
                sig,
                isForwarded
            );
        }
    }
}
