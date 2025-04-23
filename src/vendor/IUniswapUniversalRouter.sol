// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {PoolKey} from "@uniswapv4/types/PoolKey.sol";
import {IAllowanceTransfer} from "@permit2/interfaces/IAllowanceTransfer.sol";

interface IUniswapV4Router {
    struct ExactInputSingleParams {
        PoolKey poolKey;
        bool zeroForOne;
        uint128 amountIn;
        uint128 amountOutMinimum;
        bytes hookData;
    }
}

interface IUniswapUniversalRouter {
    function execute(bytes calldata commands, bytes[] calldata inputs, uint256 deadline) external payable;
    function execute(bytes calldata commands, bytes[] calldata inputs) external payable;
}

bytes1 constant COMMAND_V2_EXACT_IN = 0x08;
bytes1 constant COMMAND_V3_EXACT_IN = 0x00;
bytes1 constant COMMAND_V4_SWAP = 0x10; // abi.decode(params, (bytes, bytes[])) where the first bytes is a list of commands and the second one is a list of arguments

bytes1 constant SUBCOMMAND_V4_SWAP_EXACT_IN_SINGLE = 0x06; // IV4Router.ExactInputSingleParams calldata swapParams = params.decodeSwapExactInSingleParams(); this is just abi.encode(swapParams);

bytes1 constant SUBCOMMAND_V4_SETTLE_ALL = 0x0c; // (Currency currency, uint256 maxAmount) = params.decodeCurrencyAndUint256(); this is just abi.encode(currency, maxAmount);
bytes1 constant SUBCOMMAND_V4_TAKE_ALL = 0x0f; // (Currency currency, uint256 minAmount) = params.decodeCurrencyAndUint256(); this is just abi.encode(currency, minAmount);


bytes1 constant COMMAND_PERMIT2_PERMIT = 0x0a;
bytes1 constant COMMAND_PERMIT2_TRANSFER_FROM = 0x02;
bytes1 constant COMMAND_WRAP_ETH = 0x0b;
bytes1 constant COMMAND_UNWRAP_WETH = 0x0c;
