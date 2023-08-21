// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {WETH} from "solmate/src/tokens/WETH.sol";

abstract contract WethWrap {
    /// @dev WETH address
    WETH private immutable _weth;

    constructor(address payable weth) {
        _weth = WETH(weth);
    }

    function depositWeth(uint256 amount) internal {
        _weth.deposit{value: amount}();
    }

    function withdrawWeth(uint256 amount) internal {
        _weth.withdraw(amount);
    }
}
