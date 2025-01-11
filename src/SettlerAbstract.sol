// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {Permit2PaymentAbstract} from "./core/Permit2PaymentAbstract.sol";

abstract contract SettlerAbstract is Permit2PaymentAbstract {
    uint256 internal constant BASIS = 10_000;
    IERC20 internal constant ETH_ADDRESS = IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE);

    function _hasMetaTxn() internal pure virtual returns (bool);

    function _tokenId() internal pure virtual returns (uint256);

    function _dispatch(uint256 action, bytes calldata data) internal virtual returns (bool);
}
