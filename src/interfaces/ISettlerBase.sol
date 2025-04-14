// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

interface ISettlerBase {
    struct AllowedSlippage {
        address payable recipient;
        IERC20 buyToken;
        uint256 minAmountOut;
    }
}
