// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {Currency} from "@uniswapv4/types/Currency.sol";
import {IHooks} from "@uniswapv4/interfaces/IHooks.sol";
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

IUniswapUniversalRouter constant UNIVERSAL_ROUTER = IUniswapUniversalRouter(0x66a9893cC07D91D95644AEDD05D03f95e1dBA8Af);

bytes1 constant COMMAND_V2_EXACT_IN = 0x08;
bytes1 constant COMMAND_V3_EXACT_IN = 0x00;
bytes1 constant COMMAND_V4_SWAP = 0x10;

bytes1 constant SUBCOMMAND_V4_SWAP_EXACT_IN_SINGLE = 0x06;
bytes1 constant SUBCOMMAND_V4_SETTLE = 0x0b;
bytes1 constant SUBCOMMAND_V4_TAKE_ALL = 0x0f;

bytes1 constant COMMAND_PERMIT2_PERMIT = 0x0a;
bytes1 constant COMMAND_WRAP_ETH = 0x0b;
bytes1 constant COMMAND_UNWRAP_WETH = 0x0c;

uint256 constant CONTRACT_BALANCE = 0x8000000000000000000000000000000000000000000000000000000000000000;
uint256 constant ALREADY_PAID = 0;
uint128 constant OPEN_DELTA = 0;
address constant RECIPIENT_ROUTER = address(2);
address constant RECIPIENT_TAKER = address(1);

function encodeV2Swap(
    address recipient,
    uint256 amountIn,
    uint256 amountOutMin,
    IERC20 sellToken,
    IERC20 buyToken,
    bool payerIsUser
) pure returns (bytes1, bytes memory) {
    address[] memory path = new address[](2);
    path[0] = address(sellToken);
    path[1] = address(buyToken);
    return (COMMAND_V2_EXACT_IN, abi.encode(recipient, amountIn, amountOutMin, path, payerIsUser));
}

function encodeV3Swap(
    address recipient,
    uint256 amountIn,
    uint256 amountOutMin,
    IERC20 sellToken,
    uint24 feeTier,
    IERC20 buyToken,
    bool payerIsUser
) pure returns (bytes1, bytes memory) {
    bytes memory path = abi.encodePacked(sellToken, feeTier, buyToken);
    return (COMMAND_V3_EXACT_IN, abi.encode(recipient, amountIn, amountOutMin, path, payerIsUser));
}

function encodeV3Swap(address recipient, uint256 amountIn, uint256 amountOutMin, bytes memory path, bool payerIsUser)
    pure
    returns (bytes1, bytes memory)
{
    return (COMMAND_V3_EXACT_IN, abi.encode(recipient, amountIn, amountOutMin, path, payerIsUser));
}

function encodeV4Swap(
    address recipient,
    uint256 amountIn,
    uint256 amountOutMin,
    IERC20 sellToken,
    uint24 feeTier,
    int24 tickSpacing,
    address hook,
    IERC20 buyToken,
    bool payerIsUser
) pure returns (bytes1, bytes memory) {
    Currency currency0;
    Currency currency1;
    bool zeroForOne;
    if (address(sellToken) == 0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE) {
        sellToken = IERC20(address(0));
        currency1 = Currency.wrap(address(buyToken));
        zeroForOne = true;
    } else if (address(buyToken) == 0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE) {
        buyToken = IERC20(address(0));
        currency1 = Currency.wrap(address(sellToken));
    } else if (sellToken < buyToken) {
        currency0 = Currency.wrap(address(sellToken));
        currency1 = Currency.wrap(address(buyToken));
        zeroForOne = true;
    } else {
        currency0 = Currency.wrap(address(buyToken));
        currency1 = Currency.wrap(address(sellToken));
    }
    IUniswapV4Router.ExactInputSingleParams memory params = IUniswapV4Router.ExactInputSingleParams({
        poolKey: PoolKey({
            currency0: currency0,
            currency1: currency1,
            fee: feeTier,
            tickSpacing: tickSpacing,
            hooks: IHooks(hook)
        }),
        zeroForOne: zeroForOne,
        amountIn: OPEN_DELTA,
        amountOutMinimum: 0,
        hookData: ""
    });

    bytes memory commands =
        abi.encodePacked(SUBCOMMAND_V4_SETTLE, SUBCOMMAND_V4_SWAP_EXACT_IN_SINGLE, SUBCOMMAND_V4_TAKE_ALL);
    bytes[] memory args = new bytes[](3);
    args[0] = abi.encode(sellToken, amountIn, payerIsUser);
    args[1] = abi.encode(params);
    args[2] = abi.encode(buyToken, amountOutMin);

    return (COMMAND_V4_SWAP, abi.encode(commands, args));
}

function encodePermit2Permit(IERC20 token, uint48 nonce, bytes memory signature) pure returns (bytes1, bytes memory) {
    IAllowanceTransfer.PermitSingle memory permit = IAllowanceTransfer.PermitSingle({
        details: IAllowanceTransfer.PermitDetails({
            token: address(token),
            amount: type(uint160).max,
            expiration: type(uint48).max,
            nonce: nonce
        }),
        spender: address(UNIVERSAL_ROUTER),
        sigDeadline: type(uint256).max
    });

    return (COMMAND_PERMIT2_PERMIT, abi.encode(permit, signature));
}

function encodeWrapEth(address recipient, uint256 amount) pure returns (bytes1, bytes memory) {
    return (COMMAND_WRAP_ETH, abi.encode(recipient, amount));
}

function encodeUnwrapWeth(address recipient, uint256 amountOutMin) pure returns (bytes1, bytes memory) {
    return (COMMAND_UNWRAP_WETH, abi.encode(recipient, amountOutMin));
}
