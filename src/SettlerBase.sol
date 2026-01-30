// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {IERC721Owner} from "./IERC721Owner.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerBase} from "./interfaces/ISettlerBase.sol";

import {uint512} from "./utils/512Math.sol";

import {DEPLOYER} from "./deployer/DeployerAddress.sol";

import {Basic} from "./core/Basic.sol";
import {RfqOrderSettlement} from "./core/RfqOrderSettlement.sol";
import {UniswapV3Fork} from "./core/UniswapV3Fork.sol";
import {UniswapV2} from "./core/UniswapV2.sol";
import {Velodrome, IVelodromePair} from "./core/Velodrome.sol";

import {SafeTransferLib} from "./vendor/SafeTransferLib.sol";
import {Ternary} from "./utils/Ternary.sol";

import {ISettlerActions} from "./ISettlerActions.sol";
import {revertTooMuchSlippage} from "./core/SettlerErrors.sol";

/// @dev This library's ABIDecoding is more lax than the Solidity ABIDecoder. This library omits index bounds/overflow
/// checking when accessing calldata arrays for gas efficiency. It also omits checks against `calldatasize()`. This
/// means that it is possible that `args` will run off the end of calldata and be implicitly padded with zeroes. That we
/// don't check for overflow means that offsets can be negative. This can also result in `args` that alias other parts
/// of calldata, or even the `actions` array itself.
library CalldataDecoder {
    function decodeCall(bytes[] calldata data, uint256 i)
        internal
        pure
        returns (uint256 selector, bytes calldata args)
    {
        assembly ("memory-safe") {
            // initially, we set `args.offset` to the pointer to the length. this is 32 bytes before the actual start of data
            args.offset :=
                add(
                    data.offset,
                    // We allow the indirection/offset to `calls[i]` to be negative
                    calldataload(i)
                )
            // now we load `args.length` and set `args.offset` to the start of data
            args.length := calldataload(args.offset)
            args.offset := add(0x20, args.offset)

            // slice off the first 4 bytes of `args` as the selector
            selector := shr(0xe0, calldataload(args.offset))
            args.length := sub(args.length, 0x04)
            args.offset := add(0x04, args.offset)
        }
    }
}

abstract contract SettlerBase is ISettlerBase, Basic, RfqOrderSettlement, UniswapV3Fork, UniswapV2, Velodrome {
    using SafeTransferLib for IERC20;
    using SafeTransferLib for address payable;
    using Ternary for bool;

    receive() external payable {}

    event GitCommit(bytes20 indexed);

    // When/if you change this, you must make corresponding changes to
    // `sh/deploy_new_chain.sh` and 'sh/common_deploy_settler.sh' to set
    // `constructor_args`.
    constructor(bytes20 gitCommit) {
        if (block.chainid != 31337) {
            emit GitCommit(gitCommit);
            assert(IERC721Owner(DEPLOYER).ownerOf(_tokenId()) == address(this));
        } else {
            assert(gitCommit == bytes20(0));
        }
    }

    function _div512to256(uint512 n, uint512 d) internal view virtual override returns (uint256) {
        return n.div(d);
    }

    function _mandatorySlippageCheck() internal pure virtual returns (bool) {
        return false;
    }

    function _slippagePreBalance(AllowedSlippage calldata slippage) internal view returns (bool skip, uint256 preBalance) {
        (, IERC20 buyToken, uint256 minAmountOut) = (slippage.recipient, slippage.buyToken, slippage.minAmountOut);
        if (minAmountOut == 0 && address(buyToken) == address(0)) {
            return (true, 0);
        }
        bool isETH = (buyToken == ETH_ADDRESS);
        if (isETH) {
            preBalance = address(this).balance - msg.value;
        } else {
            preBalance = buyToken.fastBalanceOf(address(this));
        }
        return (false, preBalance);
    }

    function _checkSlippageAndTransfer(AllowedSlippage calldata slippage, uint256 preBalance) internal {
        // This final slippage check effectively prohibits custody optimization on the
        // final hop of every swap. This is gas-inefficient. This is on purpose. Because
        // ISettlerActions.BASIC could interact with an intents-based settlement
        // mechanism, we must ensure that the user's want token increase is coming
        // directly from us instead of from some other form of exchange of value.
        (address payable recipient, IERC20 buyToken, uint256 minAmountOut) =
            (slippage.recipient, slippage.buyToken, slippage.minAmountOut);
        if (_mandatorySlippageCheck()) {
            require(minAmountOut != 0);
        } else if (minAmountOut == 0 && address(buyToken) == address(0)) {
            return;
        }
        bool isETH = (buyToken == ETH_ADDRESS);
        uint256 amountOut = isETH ? address(this).balance : buyToken.fastBalanceOf(address(this));
        uint256 delta;
        if (amountOut > preBalance) {
            delta = amountOut - preBalance;
        }
        if (delta < minAmountOut) {
            revertTooMuchSlippage(buyToken, minAmountOut, delta);
        }
        if (delta == 0) {
            return;
        }
        if (isETH) {
            recipient.safeTransferETH(delta);
        } else {
            buyToken.safeTransfer(recipient, delta);
        }
    }

    function _dispatch(uint256, uint256 action, bytes calldata data) internal virtual override returns (bool) {
        //// NOTICE: This function has been largely copy/paste'd into
        //// `src/chains/Mainnet/Common.sol:MainnetMixin._dispatch`. If you make changes here, you
        //// need to make sure that corresponding changes are made to that function.

        if (action == uint32(ISettlerActions.RFQ.selector)) {
            (
                address recipient,
                ISignatureTransfer.PermitTransferFrom memory permit,
                address maker,
                bytes memory makerSig,
                IERC20 takerToken,
                uint256 maxTakerAmount
            ) = abi.decode(data, (address, ISignatureTransfer.PermitTransferFrom, address, bytes, IERC20, uint256));

            fillRfqOrderSelfFunded(recipient, permit, maker, makerSig, takerToken, maxTakerAmount);
        } else if (action == uint32(ISettlerActions.UNISWAPV3.selector)) {
            (address recipient, uint256 bps, bytes memory path, uint256 amountOutMin) =
                abi.decode(data, (address, uint256, bytes, uint256));

            sellToUniswapV3(recipient, bps, path, amountOutMin);
        } else if (action == uint32(ISettlerActions.UNISWAPV2.selector)) {
            (address recipient, address sellToken, uint256 bps, address pool, uint24 swapInfo, uint256 amountOutMin) =
                abi.decode(data, (address, address, uint256, address, uint24, uint256));

            sellToUniswapV2(recipient, sellToken, bps, pool, swapInfo, amountOutMin);
        } else if (action == uint32(ISettlerActions.BASIC.selector)) {
            (IERC20 sellToken, uint256 bps, address pool, uint256 offset, bytes memory _data) =
                abi.decode(data, (IERC20, uint256, address, uint256, bytes));

            basicSellToPool(sellToken, bps, pool, offset, _data);
        } else if (action == uint32(ISettlerActions.VELODROME.selector)) {
            (address recipient, uint256 bps, IVelodromePair pool, uint24 swapInfo, uint256 minAmountOut) =
                abi.decode(data, (address, uint256, IVelodromePair, uint24, uint256));

            sellToVelodrome(recipient, bps, pool, swapInfo, minAmountOut);
        } else if (action == uint32(ISettlerActions.POSITIVE_SLIPPAGE.selector)) {
            (address payable recipient, IERC20 token, uint256 expectedAmount, uint256 maxBps) =
                abi.decode(data, (address, IERC20, uint256, uint256));
            bool isETH = (token == ETH_ADDRESS);
            uint256 balance = isETH ? address(this).balance : token.fastBalanceOf(address(this));
            if (balance > expectedAmount) {
                uint256 cap;
                unchecked {
                    cap = balance * maxBps / BASIS;
                    balance -= expectedAmount;
                }
                balance = (balance > cap).ternary(cap, balance);
                if (isETH) {
                    recipient.safeTransferETH(balance);
                } else {
                    token.safeTransfer(recipient, balance);
                }
            }
        } else {
            return false;
        }
        return true;
    }
}
