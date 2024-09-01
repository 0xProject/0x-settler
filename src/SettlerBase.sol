// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "forge-std/interfaces/IERC20.sol";
import {IERC721Owner} from "./IERC721Owner.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

import {Basic} from "./core/Basic.sol";
import {RfqOrderSettlement} from "./core/RfqOrderSettlement.sol";
import {UniswapV3Fork} from "./core/UniswapV3Fork.sol";
import {UniswapV2} from "./core/UniswapV2.sol";
import {Velodrome, IVelodromePair} from "./core/Velodrome.sol";

import {SafeTransferLib} from "./vendor/SafeTransferLib.sol";

import {ISettlerActions} from "./ISettlerActions.sol";
import {TooMuchSlippage} from "./core/SettlerErrors.sol";

/// @dev This library's ABIDeocding is more lax than the Solidity ABIDecoder. This library omits index bounds/overflow
/// checking when accessing calldata arrays for gas efficiency. It also omits checks against `calldatasize()`. This
/// means that it is possible that `args` will run off the end of calldata and be implicitly padded with zeroes. That we
/// don't check for overflow means that offsets can be negative. This can also result in `args` that alias other parts
/// of calldata, or even the `actions` array itself.
library CalldataDecoder {
    function decodeCall(bytes[] calldata data, uint256 i)
        internal
        pure
        returns (bytes4 selector, bytes calldata args)
    {
        assembly ("memory-safe") {
            // initially, we set `args.offset` to the pointer to the length. this is 32 bytes before the actual start of data
            args.offset :=
                add(
                    data.offset,
                    // We allow the indirection/offset to `calls[i]` to be negative
                    calldataload(
                        add(shl(5, i), data.offset) // can't overflow; we assume `i` is in-bounds
                    )
                )
            // now we load `args.length` and set `args.offset` to the start of data
            args.length := calldataload(args.offset)
            args.offset := add(args.offset, 0x20)

            // slice off the first 4 bytes of `args` as the selector
            selector := calldataload(args.offset) // solidity cleans dirty bits automatically
            args.length := sub(args.length, 0x04)
            args.offset := add(args.offset, 0x04)
        }
    }
}

abstract contract SettlerBase is Basic, RfqOrderSettlement, UniswapV3Fork, UniswapV2, Velodrome {
    using SafeTransferLib for IERC20;
    using SafeTransferLib for address payable;

    receive() external payable {}

    event GitCommit(bytes20 indexed);

    constructor(bytes20 gitCommit, uint256 tokenId) {
        if (block.chainid != 31337) {
            emit GitCommit(gitCommit);
            assert(IERC721Owner(0x00000000000004533Fe15556B1E086BB1A72cEae).ownerOf(tokenId) == address(this));
        } else {
            assert(gitCommit == bytes20(0));
        }
    }

    struct AllowedSlippage {
        address recipient;
        IERC20 buyToken;
        uint256 minAmountOut;
    }

    function _checkSlippageAndTransfer(AllowedSlippage calldata slippage) internal {
        // This final slippage check effectively prohibits custody optimization on the
        // final hop of every swap. This is gas-inefficient. This is on purpose. Because
        // ISettlerActions.BASIC could interact with an intents-based settlement
        // mechanism, we must ensure that the user's want token increase is coming
        // directly from us instead of from some other form of exchange of value.
        (address recipient, IERC20 buyToken, uint256 minAmountOut) =
            (slippage.recipient, slippage.buyToken, slippage.minAmountOut);
        if (minAmountOut != 0 || address(buyToken) != address(0)) {
            if (buyToken == ETH_ADDRESS) {
                uint256 amountOut = address(this).balance;
                if (amountOut < minAmountOut) {
                    revert TooMuchSlippage(buyToken, minAmountOut, amountOut);
                }
                payable(recipient).safeTransferETH(amountOut);
            } else {
                uint256 amountOut = buyToken.balanceOf(address(this));
                if (amountOut < minAmountOut) {
                    revert TooMuchSlippage(buyToken, minAmountOut, amountOut);
                }
                buyToken.safeTransfer(recipient, amountOut);
            }
        }
    }

    function _dispatch(uint256, bytes4 action, bytes calldata data) internal virtual override returns (bool) {
        if (action == ISettlerActions.TRANSFER_FROM.selector) {
            (address recipient, ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) =
                abi.decode(data, (address, ISignatureTransfer.PermitTransferFrom, bytes));
            (ISignatureTransfer.SignatureTransferDetails memory transferDetails,) =
                _permitToTransferDetails(permit, recipient);
            _transferFrom(permit, transferDetails, sig);
        } else if (action == ISettlerActions.RFQ.selector) {
            (
                address recipient,
                ISignatureTransfer.PermitTransferFrom memory permit,
                address maker,
                bytes memory makerSig,
                IERC20 takerToken,
                uint256 maxTakerAmount
            ) = abi.decode(data, (address, ISignatureTransfer.PermitTransferFrom, address, bytes, IERC20, uint256));

            fillRfqOrderSelfFunded(recipient, permit, maker, makerSig, takerToken, maxTakerAmount);
        } else if (action == ISettlerActions.UNISWAPV3.selector) {
            (address recipient, uint256 bps, bytes memory path, uint256 amountOutMin) =
                abi.decode(data, (address, uint256, bytes, uint256));

            sellToUniswapV3(recipient, bps, path, amountOutMin);
        } else if (action == ISettlerActions.UNISWAPV2.selector) {
            (address recipient, address sellToken, uint256 bps, address pool, uint24 swapInfo, uint256 amountOutMin) =
                abi.decode(data, (address, address, uint256, address, uint24, uint256));

            sellToUniswapV2(recipient, sellToken, bps, pool, swapInfo, amountOutMin);
        } else if (action == ISettlerActions.BASIC.selector) {
            (IERC20 sellToken, uint256 bps, address pool, uint256 offset, bytes memory _data) =
                abi.decode(data, (IERC20, uint256, address, uint256, bytes));

            basicSellToPool(sellToken, bps, pool, offset, _data);
        } else if (action == ISettlerActions.VELODROME.selector) {
            (address recipient, uint256 bps, IVelodromePair pool, uint24 swapInfo, uint256 minAmountOut) =
                abi.decode(data, (address, uint256, IVelodromePair, uint24, uint256));

            sellToVelodrome(recipient, bps, pool, swapInfo, minAmountOut);
        } else if (action == ISettlerActions.POSITIVE_SLIPPAGE.selector) {
            (address recipient, IERC20 token, uint256 expectedAmount) = abi.decode(data, (address, IERC20, uint256));
            if (token == IERC20(ETH_ADDRESS)) {
                uint256 balance = address(this).balance;
                if (balance > expectedAmount) {
                    unchecked {
                        payable(recipient).safeTransferETH(balance - expectedAmount);
                    }
                }
            } else {
                uint256 balance = token.balanceOf(address(this));
                if (balance > expectedAmount) {
                    unchecked {
                        token.safeTransfer(recipient, balance - expectedAmount);
                    }
                }
            }
        } else {
            return false;
        }
        return true;
    }
}
