// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {WETH} from "solmate/src/tokens/WETH.sol";

abstract contract WethWrap {
    event WethDeposit(uint256 wad);
    event WethWithdrawal(uint256 wad);

    WETH private immutable _weth;

    constructor(address payable weth) {
        _weth = WETH(weth);
    }

    function depositWeth(uint256 amount) internal {
        _weth.deposit{value: amount}();
        emit WethDeposit(amount);
    }

    function withdrawWeth(uint256 amount) internal {
        _weth.withdraw(amount);
        emit WethWithdrawal(amount);
    }
}
