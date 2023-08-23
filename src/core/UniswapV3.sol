// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {ERC20} from "solmate/src/tokens/ERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

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

abstract contract UniswapV3 {
    /// @dev UniswapV3 Factory contract address prepended with '0xff' and left-aligned.
    bytes32 private immutable UNI_FF_FACTORY_ADDRESS;
    /// @dev UniswapV3 pool init code hash.
    bytes32 private immutable UNI_POOL_INIT_CODE_HASH;
    /// @dev Minimum size of an encoded swap path:
    ///      sizeof(address(inputToken) | uint24(fee) | address(outputToken))
    uint256 private constant SINGLE_HOP_PATH_SIZE = 20 + 3 + 20;
    /// @dev How many bytes to skip ahead in an encoded path to start at the next hop:
    ///      sizeof(address(inputToken) | uint24(fee))
    uint256 private constant PATH_SKIP_HOP_SIZE = 20 + 3;
    /// @dev The size of the swap callback prefix data before the Permit2 data.
    uint256 private constant SWAP_CALLBACK_PREFIX_DATA_SIZE = 0x80;
    /// @dev Minimum tick price sqrt ratio.
    uint160 internal constant MIN_PRICE_SQRT_RATIO = 4295128739;
    /// @dev Minimum tick price sqrt ratio.
    uint160 internal constant MAX_PRICE_SQRT_RATIO = 1461446703485210103287273052203988822378723970342;
    /// @dev Mask of lower 20 bytes.
    uint256 internal constant ADDRESS_MASK = 0x00ffffffffffffffffffffffffffffffffffffffff;
    /// @dev Mask of lower 3 bytes.
    uint256 private constant UINT24_MASK = 0xffffff;

    /// @dev Permit2 address
    ISignatureTransfer private immutable PERMIT2;

    constructor(address uniFactory, bytes32 poolInitCodeHash, address permit2) {
        UNI_FF_FACTORY_ADDRESS = bytes32((uint256(0xff) << 248) | (uint256(uint160(uniFactory)) << 88));
        UNI_POOL_INIT_CODE_HASH = poolInitCodeHash;
        PERMIT2 = ISignatureTransfer(permit2);
    }

    /// @dev Sell a token for another token directly against uniswap v3.
    /// @param encodedPath Uniswap-encoded path.
    /// @param bips proportion of current balance of the first token in the path to sell.
    /// @param recipient The recipient of the bought tokens. Can be zero for sender.
    /// @return buyAmount Amount of the last token in the path bought.
    function sellTokenForTokenToUniswapV3(bytes memory encodedPath, uint256 bips, address recipient)
        internal
        returns (uint256 buyAmount)
    {
        buyAmount = _swap(
            encodedPath,
            bips * ERC20(address(bytes20(encodedPath))).balanceOf(address(this)) / 10_000,
            address(this), // payer
            recipient,
            new bytes(0)
        );
    }

    /// @dev Sell a token for another token directly against uniswap v3. Payment is from the msg.sender
    ///      using a Permit2 signature.
    /// @param encodedPath Uniswap-encoded path.
    /// @param sellAmount amount of the first token in the path to sell.
    /// @param minBuyAmount Minimum amount of the last token in the path to buy.
    /// @param recipient The recipient of the bought tokens. Can be zero for sender.
    /// @param permit2Data The concatenated PermitTransferFrom, and (v,r,s) signature
    /// @return buyAmount Amount of the last token in the path bought.
    function sellTokenForTokenToUniswapV3(
        bytes memory encodedPath,
        uint256 sellAmount,
        address recipient,
        address payer,
        bytes memory permit2Data
    ) internal returns (uint256 buyAmount) {
        buyAmount = _swap(encodedPath, sellAmount, payer, recipient, permit2Data);
    }

    // Executes successive swaps along an encoded uniswap path.
    function _swap(
        bytes memory encodedPath,
        uint256 sellAmount,
        address payer,
        address recipient,
        bytes memory permit2Data
    ) private returns (uint256 buyAmount) {
        if (sellAmount != 0) {
            require(sellAmount <= uint256(type(int256).max), "UniswapV3Feature/SELL_AMOUNT_OVERFLOW");

            // Perform a swap for each hop in the path.
            bytes memory swapCallbackData;
            if (permit2Data.length != 0) {
                swapCallbackData = new bytes(SWAP_CALLBACK_PREFIX_DATA_SIZE + permit2Data.length);
            }
            while (true) {
                bool isPathMultiHop = _isPathMultiHop(encodedPath);
                bool zeroForOne;
                IUniswapV3Pool pool;
                {
                    (ERC20 inputToken, uint24 fee, ERC20 outputToken) = _decodeFirstPoolInfoFromPath(encodedPath);
                    pool = _toPool(inputToken, fee, outputToken);
                    zeroForOne = inputToken < outputToken;
                    if (permit2Data.length != 0) {
                        _updateSwapCallbackData(swapCallbackData, inputToken, outputToken, fee, payer, permit2Data);
                    }
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
                    require(_buyAmount >= 0, "UniswapV3Feature/INVALID_BUY_AMOUNT");
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
                // TODO: for multi-hop, do we need to truncate `permit2Data` and `swapCallbackData`?
            }
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
        require(encodedPath.length >= SINGLE_HOP_PATH_SIZE, "UniswapV3Feature/BAD_PATH_ENCODING");
        assembly ("memory-safe") {
            let p := add(encodedPath, 32)
            inputToken := shr(96, mload(p))
            p := add(p, 20)
            fee := shr(232, mload(p))
            p := add(p, 3)
            outputToken := shr(96, mload(p))
        }
    }

    // Skip past the first hop of an encoded uniswap path in-place.
    function _shiftHopFromPathInPlace(bytes memory encodedPath)
        private
        pure
        returns (bytes memory shiftedEncodedPath)
    {
        require(encodedPath.length >= PATH_SKIP_HOP_SIZE, "UniswapV3Feature/BAD_PATH_ENCODING");
        uint256 shiftSize = PATH_SKIP_HOP_SIZE;
        uint256 newSize = encodedPath.length - shiftSize;
        assembly ("memory-safe") {
            shiftedEncodedPath := add(encodedPath, shiftSize)
            mstore(shiftedEncodedPath, newSize)
        }
    }

    // Update `swapCallbackData` in place with new values.
    function _updateSwapCallbackData(
        bytes memory swapCallbackData,
        ERC20 inputToken,
        ERC20 outputToken,
        uint24 fee,
        address payer,
        bytes memory permit2Data
    ) private {
        assembly ("memory-safe") {
            mstore(add(swapCallbackData, 0x20), and(ADDRESS_MASK, inputToken))
            mstore(add(swapCallbackData, 0x40), and(ADDRESS_MASK, outputToken))
            mstore(add(swapCallbackData, 0x60), and(UINT24_MASK, fee))
            mstore(add(swapCallbackData, 0x80), and(ADDRESS_MASK, payer))
            for {
                let dst := add(swapCallbackData, 0xa0)
                let src := add(permit2Data, 0x20)
                let end := add(src, mload(permit2Data))
            } lt(src, end) {
                src := add(0x20, src)
                dst := add(0x20, dst)
            } { mstore(dst, mload(src)) }
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
            let p := s
            mstore(p, ffFactoryAddress)
            p := add(p, 0x15)
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

    /// @dev The UniswapV3 pool swap callback which pays the funds requested
    ///      by the caller/pool to the pool. Can only be called by a valid
    ///      UniswapV3 pool.
    /// @param amount0Delta Token0 amount owed.
    /// @param amount1Delta Token1 amount owed.
    /// @param data Arbitrary data forwarded from swap() caller. An ABI-encoded
    ///        struct of: inputToken, outputToken, fee, payer
    function uniswapV3SwapCallback(int256 amount0Delta, int256 amount1Delta, bytes calldata data) external {
        ERC20 token0;
        ERC20 token1;
        address payer;
        uint256 permit2DataLength = data.length - SWAP_CALLBACK_PREFIX_DATA_SIZE;
        bytes memory permit2Data = new bytes(permit2DataLength);
        {
            uint24 fee;
            // Decode the data.
            assembly ("memory-safe") {
                let p := add(36, calldataload(68))
                token0 := calldataload(p)
                token1 := calldataload(add(p, 32))
                fee := calldataload(add(p, 64))
                payer := calldataload(add(p, 96))

                let z := add(permit2Data, 32)
                for { let i := 0 } lt(i, div(permit2DataLength, 32)) { i := add(1, i) } {
                    mstore(add(z, mul(32, i)), calldataload(add(add(p, 128), mul(32, i))))
                }
            }
            (token0, token1) = token0 < token1 ? (token0, token1) : (token1, token0);
            // Only a valid pool contract can call this function.
            require(
                msg.sender == address(_toPool(token0, fee, token1)), "UniswapV3Feature/INVALID_SWAP_CALLBACK_CALLER"
            );
        }
        // Pay the amount owed to the pool.
        if (amount0Delta > 0) {
            _pay(token0, payer, msg.sender, uint256(amount0Delta), permit2Data);
        } else if (amount1Delta > 0) {
            _pay(token1, payer, msg.sender, uint256(amount1Delta), permit2Data);
        } else {
            revert("UniswapV3Feature/INVALID_SWAP_AMOUNTS");
        }
    }

    function _pay(ERC20 token, address payer, address to, uint256 amount, bytes memory permit2Data) private {
        if (payer == address(this)) {
            _transferERC20Tokens(token, to, amount);
        } else {
            // Single transfer permit2
            if (permit2Data.length == 288) {
                (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) =
                    abi.decode(permit2Data, (ISignatureTransfer.PermitTransferFrom, bytes));

                ISignatureTransfer.SignatureTransferDetails memory transferDetails =
                    ISignatureTransfer.SignatureTransferDetails({to: to, requestedAmount: amount});
                PERMIT2.permitTransferFrom(permit, transferDetails, payer, sig);
            } else {
                // Batch transfer permit2
                (ISignatureTransfer.PermitBatchTransferFrom memory permit, bytes memory sig) =
                    abi.decode(permit2Data, (ISignatureTransfer.PermitBatchTransferFrom, bytes));
                // TODO we only support a max batch size of 2
                ISignatureTransfer.SignatureTransferDetails[] memory transferDetails =
                    new ISignatureTransfer.SignatureTransferDetails[](permit.permitted.length);
                transferDetails[0] = ISignatureTransfer.SignatureTransferDetails({to: to, requestedAmount: amount});
                // TODO scale fee amount by the above ratio?
                // TODO fee recipient
                transferDetails[1] = ISignatureTransfer.SignatureTransferDetails({
                    to: 0x2222222222222222222222222222222222222222,
                    requestedAmount: permit.permitted[1].amount
                });
                PERMIT2.permitTransferFrom(permit, transferDetails, payer, sig);
            }
        }
    }

    /// @dev Transfers ERC20 tokens from ourselves to `to`.
    /// @param token The token to spend.
    /// @param to The recipient of the tokens.
    /// @param amount The amount of `token` to transfer.
    function _transferERC20Tokens(ERC20 token, address to, uint256 amount) internal {
        require(address(token) != address(this), "FixinTokenSpender/CANNOT_INVOKE_SELF");

        assembly ("memory-safe") {
            let ptr := mload(0x40) // free memory pointer

            // selector for transfer(address,uint256)
            mstore(ptr, 0xa9059cbb00000000000000000000000000000000000000000000000000000000)
            mstore(add(ptr, 0x04), and(ADDRESS_MASK, to))
            mstore(add(ptr, 0x24), amount)

            let success := call(gas(), token, 0, ptr, 0x44, 0x00, 0x20)

            // Check for ERC20 success. ERC20 tokens should return a boolean,
            // but some don't. We accept 0-length return data as success, or at
            // least 32 bytes that starts with a 32-byte boolean true.
            success :=
                and(
                    success, // call itself succeeded
                    or(
                        iszero(returndatasize()), // no return data, or
                        and(
                            gt(returndatasize(), 0x1f), // at least 32 bytes
                            eq(mload(0x00), 1) // starts with uint256(1)
                        )
                    )
                )

            // bubble revert reason
            if iszero(success) {
                returndatacopy(ptr, 0, returndatasize())
                revert(ptr, returndatasize())
            }
        }
    }
}
