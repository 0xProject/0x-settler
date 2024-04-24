// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "../IERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";
import {Panic} from "../utils/Panic.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {AddressDerivation} from "../utils/AddressDerivation.sol";
import {SettlerAbstract} from "../SettlerAbstract.sol";

import {TooMuchSlippage, ConfusedDeputy} from "./SettlerErrors.sol";

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

abstract contract UniswapV3 is SettlerAbstract {
    using UnsafeMath for uint256;
    using SafeTransferLib for IERC20;

    /// @dev UniswapV3 Factory contract address
    address private immutable UNI_FACTORY_ADDRESS;
    /// @dev UniswapV3 pool init code hash.
    bytes32 private immutable UNI_POOL_INIT_CODE_HASH;
    /// @dev Minimum size of an encoded swap path:
    ///      sizeof(address(inputToken) | uint24(fee) | address(outputToken))
    uint256 private constant SINGLE_HOP_PATH_SIZE = 0x2b;
    /// @dev How many bytes to skip ahead in an encoded path to start at the next hop:
    ///      sizeof(address(inputToken) | uint24(fee))
    uint256 private constant PATH_SKIP_HOP_SIZE = 0x17;
    /// @dev The size of the swap callback prefix data before the Permit2 data.
    uint256 private constant SWAP_CALLBACK_PREFIX_DATA_SIZE = 0x3f;
    /// @dev The offset from the pointer to the length of the swap callback prefix data to the start of the Permit2 data.
    uint256 private constant SWAP_CALLBACK_PERMIT2DATA_OFFSET = 0x5f;
    uint256 private constant PERMIT_DATA_SIZE = 0x80;
    uint256 private constant ISFORWARDED_DATA_SIZE = 0x20;
    /// @dev Minimum tick price sqrt ratio.
    uint160 private constant MIN_PRICE_SQRT_RATIO = 4295128739;
    /// @dev Minimum tick price sqrt ratio.
    uint160 private constant MAX_PRICE_SQRT_RATIO = 1461446703485210103287273052203988822378723970342;
    /// @dev Mask of lower 20 bytes.
    uint256 private constant ADDRESS_MASK = 0x00ffffffffffffffffffffffffffffffffffffffff;
    /// @dev Mask of lower 3 bytes.
    uint256 private constant UINT24_MASK = 0xffffff;

    constructor(address uniFactory, bytes32 poolInitCodeHash) {
        UNI_FACTORY_ADDRESS = uniFactory;
        UNI_POOL_INIT_CODE_HASH = poolInitCodeHash;
    }

    /// @dev Sell a token for another token directly against uniswap v3.
    /// @param encodedPath Uniswap-encoded path.
    /// @param bips proportion of current balance of the first token in the path to sell.
    /// @param minBuyAmount Minimum amount of the last token in the path to buy.
    /// @param recipient The recipient of the bought tokens.
    /// @return buyAmount Amount of the last token in the path bought.
    function sellTokenForTokenToUniswapV3(
        address recipient,
        bytes memory encodedPath,
        uint256 bips,
        uint256 minBuyAmount
    ) internal returns (uint256 buyAmount) {
        buyAmount = _swap(
            recipient,
            encodedPath,
            // We don't care about phantom overflow here because reserves are
            // limited to 128 bits. Any token balance that would overflow here
            // would also break UniV3.
            (IERC20(address(bytes20(encodedPath))).balanceOf(address(this)) * bips).unsafeDiv(10_000),
            minBuyAmount,
            address(this), // payer
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
    function sellTokenForTokenToUniswapV3VIP(
        address recipient,
        bytes memory encodedPath,
        uint256 sellAmount,
        uint256 minBuyAmount,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig
    ) internal returns (uint256 buyAmount) {
        bytes memory swapCallbackData =
            new bytes(SWAP_CALLBACK_PREFIX_DATA_SIZE + PERMIT_DATA_SIZE + ISFORWARDED_DATA_SIZE + sig.length);
        _encodePermit2Data(swapCallbackData, permit, sig, _isForwarded());

        buyAmount = _swap(recipient, encodedPath, sellAmount, minBuyAmount, _msgSender(), swapCallbackData);
    }

    /// @dev Sell a token for another token directly against uniswap v3. Payment is using a Permit2 signature.
    /// @param encodedPath Uniswap-encoded path.
    /// @param sellAmount amount of the first token in the path to sell.
    /// @param minBuyAmount Minimum amount of the last token in the path to buy.
    /// @param recipient The recipient of the bought tokens.
    /// @param payer The taker of the transaction and the signer of the permit
    /// @param permit The PermitTransferFrom allowing this contract to spend the taker's tokens
    /// @param sig The taker's signature for Permit2
    /// @return buyAmount Amount of the last token in the path bought.
    function sellTokenForTokenToUniswapV3MetaTxn(
        address recipient,
        bytes memory encodedPath,
        uint256 sellAmount,
        uint256 minBuyAmount,
        address payer,
        ISignatureTransfer.PermitTransferFrom memory permit,
        bytes memory sig
    ) internal returns (uint256 buyAmount) {
        bytes memory swapCallbackData =
            new bytes(SWAP_CALLBACK_PREFIX_DATA_SIZE + PERMIT_DATA_SIZE + ISFORWARDED_DATA_SIZE + sig.length);
        _encodePermit2Data(swapCallbackData, permit, sig, false);

        buyAmount = _swap(recipient, encodedPath, sellAmount, minBuyAmount, payer, swapCallbackData);
    }

    // Executes successive swaps along an encoded uniswap path.
    function _swap(
        address recipient,
        bytes memory encodedPath,
        uint256 sellAmount,
        uint256 minBuyAmount,
        address payer,
        bytes memory swapCallbackData
    ) private returns (uint256 buyAmount) {
        if (sellAmount > uint256(type(int256).max)) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }

        IERC20 outputToken;
        while (true) {
            bool isPathMultiHop = _isPathMultiHop(encodedPath);
            bool zeroForOne;
            IUniswapV3Pool pool;
            {
                (IERC20 token0, uint24 fee, IERC20 token1) = _decodeFirstPoolInfoFromPath(encodedPath);
                outputToken = token1;
                if (!(zeroForOne = token0 < token1)) {
                    (token0, token1) = (token1, token0);
                }
                pool = _toPool(token0, fee, token1);
                _updateSwapCallbackData(swapCallbackData, token0, fee, token1, payer);
            }

            int256 amount0;
            int256 amount1;
            if (payer == address(this)) {
                (amount0, amount1) = abi.decode(
                    _setCallbackAndCall(
                        address(pool),
                        abi.encodeCall(
                            pool.swap,
                            (
                                // Intermediate tokens go to this contract.
                                isPathMultiHop ? address(this) : recipient,
                                zeroForOne,
                                int256(sellAmount),
                                zeroForOne ? MIN_PRICE_SQRT_RATIO + 1 : MAX_PRICE_SQRT_RATIO - 1,
                                swapCallbackData
                            )
                        ),
                        _uniV3Callback
                    ),
                    (int256, int256)
                );
            } else {
                (amount0, amount1) = abi.decode(
                    _setOperatorAndCall(
                        address(pool),
                        abi.encodeCall(
                            pool.swap,
                            (
                                // Intermediate tokens go to this contract.
                                isPathMultiHop ? address(this) : recipient,
                                zeroForOne,
                                int256(sellAmount),
                                zeroForOne ? MIN_PRICE_SQRT_RATIO + 1 : MAX_PRICE_SQRT_RATIO - 1,
                                swapCallbackData
                            )
                        ),
                        _uniV3Callback
                    ),
                    (int256, int256)
                );
            }

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
    function _isPathMultiHop(bytes memory encodedPath) private pure returns (bool) {
        return encodedPath.length > SINGLE_HOP_PATH_SIZE;
    }

    function _decodeFirstPoolInfoFromPath(bytes memory encodedPath)
        private
        pure
        returns (IERC20 inputToken, uint24 fee, IERC20 outputToken)
    {
        if (encodedPath.length < SINGLE_HOP_PATH_SIZE) {
            Panic.panic(Panic.ARRAY_OUT_OF_BOUNDS);
        }
        assembly ("memory-safe") {
            // Solidity cleans dirty bits automatically
            inputToken := mload(add(encodedPath, 0x14))
            fee := mload(add(encodedPath, 0x17))
            outputToken := mload(add(encodedPath, SINGLE_HOP_PATH_SIZE))
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
            {
                let permitted := mload(permit)
                mstore(add(swapCallbackData, SWAP_CALLBACK_PERMIT2DATA_OFFSET), mload(permitted))
                mstore(add(swapCallbackData, add(SWAP_CALLBACK_PERMIT2DATA_OFFSET, 0x20)), mload(add(permitted, 0x20)))
            }
            mstore(add(swapCallbackData, add(SWAP_CALLBACK_PERMIT2DATA_OFFSET, 0x40)), mload(add(permit, 0x20)))
            mstore(add(swapCallbackData, add(SWAP_CALLBACK_PERMIT2DATA_OFFSET, 0x60)), mload(add(permit, 0x40)))
            mstore(add(swapCallbackData, add(SWAP_CALLBACK_PERMIT2DATA_OFFSET, PERMIT_DATA_SIZE)), and(isForwarded, 1))
            mcopy(
                add(
                    swapCallbackData,
                    add(add(SWAP_CALLBACK_PERMIT2DATA_OFFSET, PERMIT_DATA_SIZE), ISFORWARDED_DATA_SIZE)
                ),
                add(sig, 0x20),
                mload(sig)
            )
        }
    }

    // Update `swapCallbackData` in place with new values.
    function _updateSwapCallbackData(
        bytes memory swapCallbackData,
        IERC20 token0,
        uint24 fee,
        IERC20 token1,
        address payer
    ) private pure {
        assembly ("memory-safe") {
            let length := mload(swapCallbackData)
            mstore(add(swapCallbackData, 0x3f), payer)
            mstore(add(swapCallbackData, 0x2b), token1)
            mstore(add(swapCallbackData, 0x17), fee)
            mstore(add(swapCallbackData, 0x14), token0)
            mstore(swapCallbackData, length)
        }
    }

    // Compute the pool address given two tokens and a fee.
    function _toPool(IERC20 inputToken, uint24 fee, IERC20 outputToken) private view returns (IUniswapV3Pool) {
        // address(keccak256(abi.encodePacked(
        //     hex"ff",
        //     UNI_FACTORY_ADDRESS,
        //     keccak256(abi.encode(inputToken, outputToken, fee)),
        //     UNI_POOL_INIT_CODE_HASH
        // )))
        (IERC20 token0, IERC20 token1) =
            inputToken < outputToken ? (inputToken, outputToken) : (outputToken, inputToken);
        bytes32 salt;
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(0x00, and(ADDRESS_MASK, token0))
            mstore(0x20, and(ADDRESS_MASK, token1))
            mstore(0x40, and(UINT24_MASK, fee))
            salt := keccak256(0x00, 0x60)
            mstore(0x40, ptr)
        }
        return IUniswapV3Pool(
            AddressDerivation.deriveDeterministicContract(UNI_FACTORY_ADDRESS, salt, UNI_POOL_INIT_CODE_HASH)
        );
    }

    error ZeroSwapAmount();

    bytes4 internal constant _UNIV3_CALLBACK_SELECTOR = bytes4(keccak256("uniswapV3SwapCallback(int256,int256,bytes)"));

    function _uniV3Callback(bytes calldata data) private returns (bytes memory) {
        require(data.length >= 0x84 && bytes4(data) == _UNIV3_CALLBACK_SELECTOR);
        int256 amount0Delta;
        int256 amount1Delta;
        assembly ("memory-safe") {
            amount0Delta := calldataload(0x04)
            amount1Delta := calldataload(0x24)
            data.offset := add(0x04, calldataload(add(0x44, data.offset)))
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
    /// @param data Arbitrary data forwarded from swap() caller. A packed encoding of: inputToken, outputToken, fee, payer, permit
    function uniswapV3SwapCallback(int256 amount0Delta, int256 amount1Delta, bytes calldata data) private {
        // Decode the data.
        IERC20 token0;
        uint24 fee;
        IERC20 token1;
        address payer;
        assembly ("memory-safe") {
            {
                let firstWord := calldataload(data.offset)
                token0 := shr(0x60, firstWord)
                fee := shr(0x48, firstWord)
            }
            token1 := calldataload(add(data.offset, 0xb))
            payer := calldataload(add(data.offset, 0x1f))
        }
        if (msg.sender != address(_toPool(token0, fee, token1))) {
            revert ConfusedDeputy();
        }

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

    function _pay(IERC20 token, address payer, uint256 amount, bytes calldata permit2Data) private {
        if (payer == address(this)) {
            token.safeTransfer(msg.sender, amount);
        } else {
            (ISignatureTransfer.PermitTransferFrom memory permit, bool isForwarded) =
                abi.decode(permit2Data, (ISignatureTransfer.PermitTransferFrom, bool));
            bytes calldata sig = permit2Data[PERMIT_DATA_SIZE + ISFORWARDED_DATA_SIZE:];
            (ISignatureTransfer.SignatureTransferDetails memory transferDetails,,) =
                _permitToTransferDetails(permit, msg.sender);
            _transferFrom(permit, transferDetails, payer, sig, isForwarded);
        }
    }
}
