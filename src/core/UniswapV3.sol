// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {ERC20} from "solmate/src/tokens/ERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {FullMath} from "../utils/FullMath.sol";
import {Panic} from "../utils/Panic.sol";
import {SafeTransferLib} from "../utils/SafeTransferLib.sol";
import {Permit2PaymentAbstract} from "./Permit2Payment.sol";

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

abstract contract UniswapV3 is Permit2PaymentAbstract {
    using FullMath for uint256;
    using SafeTransferLib for ERC20;

    error TooMuchSlippage(address token, uint256 expected, uint256 actual);

    /// @dev UniswapV3 Factory contract address prepended with '0xff' and left-aligned.
    bytes32 private immutable UNI_FF_FACTORY_ADDRESS;
    /// @dev UniswapV3 pool init code hash.
    bytes32 private immutable UNI_POOL_INIT_CODE_HASH;
    /// @dev Minimum size of an encoded swap path:
    ///      sizeof(address(inputToken) | uint24(fee) | address(outputToken))
    uint256 private constant SINGLE_HOP_PATH_SIZE = 43;
    /// @dev How many bytes to skip ahead in an encoded path to start at the next hop:
    ///      sizeof(address(inputToken) | uint24(fee))
    uint256 private constant PATH_SKIP_HOP_SIZE = 23;
    /// @dev The size of the swap callback prefix data before the Permit2 data.
    uint256 private constant SWAP_CALLBACK_PREFIX_DATA_SIZE = 0x80;
    /// @dev The offset from the pointer to the length of the swap callback prefix data to the start of the Permit2 data.
    uint256 private constant SWAP_CALLBACK_PERMIT2DATA_OFFSET = 0xa0;
    uint256 private constant PERMIT_DATA_SIZE = 0x80;
    /// @dev Minimum tick price sqrt ratio.
    uint160 private constant MIN_PRICE_SQRT_RATIO = 4295128739;
    /// @dev Minimum tick price sqrt ratio.
    uint160 private constant MAX_PRICE_SQRT_RATIO = 1461446703485210103287273052203988822378723970342;
    /// @dev Mask of lower 20 bytes.
    uint256 private constant ADDRESS_MASK = 0x00ffffffffffffffffffffffffffffffffffffffff;
    /// @dev Mask of lower 3 bytes.
    uint256 private constant UINT24_MASK = 0xffffff;

    constructor(address uniFactory, bytes32 poolInitCodeHash) {
        UNI_FF_FACTORY_ADDRESS = bytes32((uint256(0xff) << 248) | (uint256(uint160(uniFactory)) << 88));
        UNI_POOL_INIT_CODE_HASH = poolInitCodeHash;
    }

    /// @dev Sell a token for another token directly against uniswap v3.
    /// @param encodedPath Uniswap-encoded path.
    /// @param bips proportion of current balance of the first token in the path to sell.
    /// @param minBuyAmount Minimum amount of the last token in the path to buy.
    /// @param recipient The recipient of the bought tokens.
    /// @return buyAmount Amount of the last token in the path bought.
    function sellTokenForTokenToUniswapV3(
        bytes memory encodedPath,
        uint256 bips,
        uint256 minBuyAmount,
        address recipient
    ) internal returns (uint256 buyAmount) {
        buyAmount = _swap(
            encodedPath,
            ERC20(address(bytes20(encodedPath))).balanceOf(address(this)).mulDiv(bips, 10_000),
            minBuyAmount,
            address(this), // payer
            recipient,
            new bytes(SWAP_CALLBACK_PREFIX_DATA_SIZE)
        );
    }

    /// @dev Sell a token for another token directly against uniswap v3. Payment is using a Permit2 signature.
    /// @param encodedPath Uniswap-encoded path.
    /// @param sellAmount amount of the first token in the path to sell.
    /// @param minBuyAmount Minimum amount of the last token in the path to buy.
    /// @param recipient The recipient of the bought tokens.
    /// @param permit The PermitTransferFrom allowing this contract to spend the taker's tokens
    /// @param sig The taker's signature for Permit2
    /// @return buyAmount Amount of the last token in the path bought.
    function sellTokenForTokenToUniswapV3(
        bytes memory encodedPath,
        uint256 sellAmount,
        uint256 minBuyAmount,
        address recipient,
        address payer,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig
    ) internal returns (uint256 buyAmount) {
        bytes memory swapCallbackData = new bytes(SWAP_CALLBACK_PREFIX_DATA_SIZE + PERMIT_DATA_SIZE + 0x20 + sig.length);
        _encodePermit2Data(swapCallbackData, permit, bytes32(0), sig);

        buyAmount = _swap(encodedPath, sellAmount, minBuyAmount, payer, recipient, swapCallbackData);
    }

    /// @dev Sell a token for another token directly against uniswap v3. Payment is using a Permit2 signature.
    /// @param encodedPath Uniswap-encoded path.
    /// @param sellAmount amount of the first token in the path to sell.
    /// @param minBuyAmount Minimum amount of the last token in the path to buy.
    /// @param recipient The recipient of the bought tokens.
    /// @param permit The PermitTransferFrom allowing this contract to spend the taker's tokens
    /// @param sig The taker's signature for Permit2
    /// @param witness Hashed additional data to be combined with _uniV3WitnessTypeString(), signed over, and verified by Permit2
    /// @return buyAmount Amount of the last token in the path bought.
    function sellTokenForTokenToUniswapV3(
        bytes memory encodedPath,
        uint256 sellAmount,
        uint256 minBuyAmount,
        address recipient,
        address payer,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig,
        bytes32 witness
    ) internal returns (uint256 buyAmount) {
        bytes memory swapCallbackData = new bytes(SWAP_CALLBACK_PREFIX_DATA_SIZE + PERMIT_DATA_SIZE + 0x20 + sig.length);
        _encodePermit2Data(swapCallbackData, permit, witness, sig);

        buyAmount = _swap(encodedPath, sellAmount, minBuyAmount, payer, recipient, swapCallbackData);
    }

    function _uniV3WitnessTypeString() internal view virtual returns (string memory);

    // Executes successive swaps along an encoded uniswap path.
    function _swap(
        bytes memory encodedPath,
        uint256 sellAmount,
        uint256 minBuyAmount,
        address payer,
        address recipient,
        bytes memory swapCallbackData
    ) private returns (uint256 buyAmount) {
        if (sellAmount > uint256(type(int256).max)) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }

        ERC20 outputToken;
        while (true) {
            bool isPathMultiHop = _isPathMultiHop(encodedPath);
            bool zeroForOne;
            IUniswapV3Pool pool;
            {
                ERC20 inputToken;
                uint24 fee;
                (inputToken, fee, outputToken) = _decodeFirstPoolInfoFromPath(encodedPath);
                pool = _toPool(inputToken, fee, outputToken);
                zeroForOne = inputToken < outputToken;
                _updateSwapCallbackData(swapCallbackData, inputToken, outputToken, fee, payer);
            }
            (int256 amount0, int256 amount1) = pool.swap(
                // Intermediate tokens go to this contract.
                isPathMultiHop ? address(this) : recipient,
                zeroForOne,
                int256(sellAmount),
                zeroForOne ? MIN_PRICE_SQRT_RATIO + 1 : MAX_PRICE_SQRT_RATIO - 1,
                swapCallbackData
            );
            {
                int256 _buyAmount = -(zeroForOne ? amount1 : amount0);
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
            revert TooMuchSlippage(address(outputToken), minBuyAmount, buyAmount);
        }
    }

    // Return whether or not an encoded uniswap path contains more than one hop.
    function _isPathMultiHop(bytes memory encodedPath) private pure returns (bool isMultiHop) {
        return encodedPath.length > SINGLE_HOP_PATH_SIZE;
    }

    function _decodeFirstPoolInfoFromPath(bytes memory encodedPath)
        private
        pure
        returns (ERC20 inputToken, uint24 fee, ERC20 outputToken)
    {
        if (encodedPath.length < SINGLE_HOP_PATH_SIZE) {
            Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
        }
        assembly ("memory-safe") {
            let p := add(encodedPath, 0x20)
            inputToken := shr(0x60, mload(p))
            p := add(p, 0x14)
            fee := shr(0xe8, mload(p))
            p := add(p, 0x03)
            outputToken := shr(0x60, mload(p))
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
        bytes32 witness,
        bytes memory sig
    ) private view {
        assembly ("memory-safe") {
            function _memcpy(dst, src, len) {
                if or(iszero(returndatasize()), iszero(staticcall(gas(), 0x04, src, len, dst, len))) { invalid() }
            }

            {
                let permitted := mload(permit)
                mstore(add(swapCallbackData, SWAP_CALLBACK_PERMIT2DATA_OFFSET), mload(permitted))
                mstore(add(swapCallbackData, add(SWAP_CALLBACK_PERMIT2DATA_OFFSET, 0x20)), mload(add(permitted, 0x20)))
            }
            mstore(add(swapCallbackData, add(SWAP_CALLBACK_PERMIT2DATA_OFFSET, 0x40)), mload(add(permit, 0x20)))
            mstore(add(swapCallbackData, add(SWAP_CALLBACK_PERMIT2DATA_OFFSET, 0x60)), mload(add(permit, 0x40)))
            mstore(add(swapCallbackData, add(SWAP_CALLBACK_PERMIT2DATA_OFFSET, PERMIT_DATA_SIZE)), witness)
            _memcpy(
                add(swapCallbackData, add(add(SWAP_CALLBACK_PERMIT2DATA_OFFSET, PERMIT_DATA_SIZE), 0x20)),
                add(sig, 0x20),
                mload(sig)
            )
        }
    }

    // Update `swapCallbackData` in place with new values.
    function _updateSwapCallbackData(
        bytes memory swapCallbackData,
        ERC20 inputToken,
        ERC20 outputToken,
        uint24 fee,
        address payer
    ) private pure {
        assembly ("memory-safe") {
            mstore(add(swapCallbackData, 0x20), and(ADDRESS_MASK, inputToken))
            mstore(add(swapCallbackData, 0x40), and(ADDRESS_MASK, outputToken))
            mstore(add(swapCallbackData, 0x60), and(UINT24_MASK, fee))
            mstore(add(swapCallbackData, 0x80), and(ADDRESS_MASK, payer))
        }
    }

    // Compute the pool address given two tokens and a fee.
    function _toPool(ERC20 inputToken, uint24 fee, ERC20 outputToken) private view returns (IUniswapV3Pool pool) {
        // address(keccak256(abi.encodePacked(
        //     hex"ff",
        //     UNI_FACTORY_ADDRESS,
        //     keccak256(abi.encode(inputToken, outputToken, fee)),
        //     UNI_POOL_INIT_CODE_HASH
        // )))
        bytes32 ffFactoryAddress = UNI_FF_FACTORY_ADDRESS;
        bytes32 poolInitCodeHash = UNI_POOL_INIT_CODE_HASH;
        (ERC20 token0, ERC20 token1) = inputToken < outputToken ? (inputToken, outputToken) : (outputToken, inputToken);
        assembly ("memory-safe") {
            let s := mload(0x40)
            mstore(s, ffFactoryAddress)
            let p := add(s, 0x15)
            // Compute the inner hash in-place
            mstore(p, and(ADDRESS_MASK, token0))
            mstore(add(p, 0x20), and(ADDRESS_MASK, token1))
            mstore(add(p, 0x40), and(UINT24_MASK, fee))
            mstore(p, keccak256(p, 0x60))
            // compute the address
            mstore(add(p, 0x20), poolInitCodeHash)
            pool := keccak256(s, 0x55) // solidity clears dirty bits for us
        }
    }

    error ZeroSwapAmount();

    /// @dev The UniswapV3 pool swap callback which pays the funds requested
    ///      by the caller/pool to the pool. Can only be called by a valid
    ///      UniswapV3 pool.
    /// @param amount0Delta Token0 amount owed.
    /// @param amount1Delta Token1 amount owed.
    /// @param data Arbitrary data forwarded from swap() caller. An ABI-encoded
    ///        struct of: inputToken, outputToken, fee, payer
    function uniswapV3SwapCallback(int256 amount0Delta, int256 amount1Delta, bytes calldata data) external {
        // Decode the data.
        (ERC20 token0, ERC20 token1, uint24 fee, address payer) = abi.decode(data, (ERC20, ERC20, uint24, address));
        (token0, token1) = token0 < token1 ? (token0, token1) : (token1, token0);
        // Only a valid pool contract can call this function.
        require(msg.sender == address(_toPool(token0, fee, token1)));

        bytes calldata permit2Data = data[SWAP_CALLBACK_PREFIX_DATA_SIZE:];
        // Pay the amount owed to the pool.
        if (amount0Delta > 0) {
            _pay(token0, payer, uint256(amount0Delta), permit2Data);
        } else if (amount1Delta > 0) {
            _pay(token1, payer, uint256(amount1Delta), permit2Data);
        } else {
            revert ZeroSwapAmount();
        }
    }

    function _pay(ERC20 token, address payer, uint256 amount, bytes calldata permit2Data) private {
        if (payer == address(this)) {
            token.safeTransfer(msg.sender, amount);
        } else {
            (ISignatureTransfer.PermitTransferFrom memory permit, bytes32 witness) =
                abi.decode(permit2Data, (ISignatureTransfer.PermitTransferFrom, bytes32));
            bytes calldata sig = permit2Data[PERMIT_DATA_SIZE + 0x20:];
            (ISignatureTransfer.SignatureTransferDetails memory transferDetails,,) =
                _permitToTransferDetails(permit, msg.sender);
            if (witness == bytes32(0)) {
                _permit2TransferFrom(permit, transferDetails, payer, sig);
            } else {
                _permit2TransferFrom(permit, transferDetails, payer, witness, _uniV3WitnessTypeString(), sig);
            }
        }
    }
}
