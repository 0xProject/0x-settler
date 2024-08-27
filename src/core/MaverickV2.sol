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
// For chains: mainnet, base, bnb, arbitrum, scroll, sepolia
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

    /**
     * @notice Pool tokenA.  Address of tokenA is such that tokenA < tokenB.
     */
    function tokenA() external view returns (IERC20);

    /**
     * @notice Pool tokenB.
     */
    function tokenB() external view returns (IERC20);

    /**
     * @notice State of the pool.
     * @param reserveA Pool tokenA balanceOf at end of last operation
     * @param reserveB Pool tokenB balanceOf at end of last operation
     * @param lastTwaD8 Value of log time weighted average price at last block.
     * Value is 8-decimal scale and is in the fractional tick domain.  E.g. a
     * value of 12.3e8 indicates the TWAP was 3/10ths of the way into the 12th
     * tick.
     * @param lastLogPriceD8 Value of log price at last block. Value is
     * 8-decimal scale and is in the fractional tick domain.  E.g. a value of
     * 12.3e8 indicates the price was 3/10ths of the way into the 12th tick.
     * @param lastTimestamp Last block.timestamp value in seconds for latest
     * swap transaction.
     * @param activeTick Current tick position that contains the active bins.
     * @param isLocked Pool isLocked, E.g., locked or unlocked; isLocked values
     * defined in Pool.sol.
     * @param binCounter Index of the last bin created.
     * @param protocolFeeRatioD3 Ratio of the swap fee that is kept for the
     * protocol.
     */
    struct State {
        uint128 reserveA;
        uint128 reserveB;
        int64 lastTwaD8;
        int64 lastLogPriceD8;
        uint40 lastTimestamp;
        int32 activeTick;
        bool isLocked;
        uint32 binCounter;
        uint8 protocolFeeRatioD3;
    }

    /**
     * @notice External function to get the state of the pool.
     */
    function getState() external view returns (State memory);
}

interface IMaverickV2SwapCallback {
    function maverickV2SwapCallback(IERC20 tokenIn, uint256 amountIn, uint256 amountOut, bytes calldata data)
        external;
}

abstract contract MaverickV2 is SettlerAbstract {
    using UnsafeMath for uint256;
    using SafeTransferLib for IERC20;

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
        bytes32 salt,
        bool tokenAIn,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig,
        uint256 minBuyAmount
    ) internal returns (uint256 buyAmount) {
        bytes memory swapCallbackData = _encodeSwapCallback(permit, sig);
        address pool = AddressDerivation.deriveDeterministicContract(maverickV2Factory, salt, maverickV2InitHash);
        (, buyAmount) = abi.decode(
            _setOperatorAndCall(
                pool,
                abi.encodeCall(
                    IMaverickV2Pool.swap,
                    (
                        recipient,
                        IMaverickV2Pool.SwapParams({
                            amount: _permitToSellAmount(permit),
                            tokenAIn: tokenAIn,
                            exactOutput: false,
                            // TODO: actually set a tick limit so that we can partial fill
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
            IERC20 buyToken = tokenAIn ? IMaverickV2Pool(pool).tokenB() : IMaverickV2Pool(pool).tokenA();
            revert TooMuchSlippage(buyToken, minBuyAmount, buyAmount);
        }
    }

    function sellToMaverickV2(
        address recipient,
        IERC20 sellToken,
        uint256 bps,
        IMaverickV2Pool pool,
        bool tokenAIn,
        uint256 minBuyAmount
    ) internal returns (uint256 buyAmount) {
        uint256 sellAmount;
        if (bps != 0) {
            unchecked {
                // We don't care about phantom overflow here because reserves
                // are limited to 128 bits. Any token balance that would
                // overflow here would also break MaverickV2.
                sellAmount = (sellToken.balanceOf(address(this)) * bps).unsafeDiv(BASIS);
            }
        }
        if (sellAmount == 0) {
            sellAmount = sellToken.balanceOf(address(pool));
            IMaverickV2Pool.State memory poolState = pool.getState();
            unchecked {
                sellAmount -= tokenAIn ? poolState.reserveA : poolState.reserveB;
            }
        } else {
            sellToken.safeTransfer(address(pool), sellAmount);
        }
        (, buyAmount) = pool.swap(
            recipient,
            IMaverickV2Pool.SwapParams({
                amount: sellAmount,
                tokenAIn: tokenAIn,
                exactOutput: false,
                // TODO: actually set a tick limit so that we can partial fill
                tickLimit: tokenAIn ? type(int32).max : type(int32).min
            }),
            new bytes(0)
        );
        if (buyAmount < minBuyAmount) {
            revert TooMuchSlippage(tokenAIn ? pool.tokenB() : pool.tokenA(), minBuyAmount, buyAmount);
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
            data.length := calldataload(add(0x80, data.offset))
            data.offset := add(0xa0, data.offset)
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
        assert(tokenIn == IERC20(permit.permitted.token));
        ISignatureTransfer.SignatureTransferDetails memory transferDetails =
            ISignatureTransfer.SignatureTransferDetails({to: msg.sender, requestedAmount: amountIn});
        _transferFrom(permit, transferDetails, data, isForwarded);
    }
}
