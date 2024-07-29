// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";
import {AddressDerivation} from "../utils/AddressDerivation.sol";

import {TooMuchSlippage} from "./SettlerErrors.sol";

// Maverick AMM V2 is not open-source. The source code was disclosed to the
// developers of 0x Settler confidentially and recompiled privately. The
// deployed bytecode inithash matches the privately recompiled inithash.
bytes32 maverickV2InitHash = 0xbb7b783eb4b8ca46925c5384a6b9919df57cb83da8f76e37291f58d0dd5c439a;

// https://docs.mav.xyz/technical-reference/contract-addresses/v2-contract-addresses
// For chains: mainnet, base, bnb, arbitrum, scroll
address maverickV2Factory = 0x0A7e848Aca42d879EF06507Fca0E7b33A0a63c1e;

interface IMaverickV2Pool {
    struct SwapParams {
        uint256 amount;
        bool tokenAIn;
        bool exactOutput;
        int32 tickLimit;
    }

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

    function sellToMaverickV2VIP(
        address recipient,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig,
        uint256 minBuyAmount
    ) internal returns (uint256 buyAmount) {
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
            tokenIn, amountIn, 0, /* we didn't bother loading `amountOut` because we don't use it */ data
        );
        return new bytes(0);
    }

    function maverickV2SwapCallback(IERC20 tokenIn, uint256 amountIn, uint256, bytes calldata data) private {}
}
