// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {WETH} from "solmate/src/tokens/WETH.sol";
import {FullMath} from "../utils/FullMath.sol";

abstract contract WethWrap {
    using FullMath for uint256;

    event WethDeposit(uint256 wad);
    event WethWithdrawal(uint256 wad);

    WETH private immutable _weth;

    constructor(address payable weth) {
        _weth = WETH(weth);
    }

    function depositWeth(uint256 bips) internal {
        uint256 amount = address(this).balance.mulDiv(bips, 10_000);
        _weth.deposit{value: amount}();
        emit WethDeposit(amount);
    }

    function withdrawWeth(uint256 bips) internal {
        uint256 amount = _weth.balanceOf(address(this)).mulDiv(bips, 10_000);
        _weth.withdraw(amount);
        emit WethWithdrawal(amount);
    }

    receive() external payable {}
}
