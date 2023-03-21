// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {ERC20} from "solmate/src/tokens/ERC20.sol";

import {SafeTransferLib as SolmateSafeTransferLib} from "solmate/src/utils/SafeTransferLib.sol";

library SafeTransferLib {
    function safeApproveIfBelow(ERC20 token, address spender, uint256 amount) internal {
        if (token.allowance(address(this), spender) < amount) {
            safeApprove(token, spender, type(uint256).max);
        }
    }

    function safeApprove(ERC20 token, address to, uint256 amount) internal {
        SolmateSafeTransferLib.safeApprove(token, to, amount);
    }

    function safeTransfer(ERC20 token, address to, uint256 amount) internal {
        SolmateSafeTransferLib.safeTransfer(token, to, amount);
    }

    function safeTransferETH(address to, uint256 amount) internal {
        SolmateSafeTransferLib.safeTransferETH(to, amount);
    }

    function safeTransferFrom(ERC20 token, address from, address to, uint256 amount) internal {
        SolmateSafeTransferLib.safeTransferFrom(token, from, to, amount);
    }
}
