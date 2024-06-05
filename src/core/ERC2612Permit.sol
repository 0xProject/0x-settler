// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC2612} from "../IERC2612.sol";
import {SafeTransferLib} from "../vendor/SafeTransferLib.sol";
import {ConfusedDeputy} from "./SettlerErrors.sol";
import {AbstractContext} from "../Context.sol";

abstract contract ERC2612Permit is AbstractContext {
    using SafeTransferLib for IERC2612;

    function erc2612PermitAndTransfer(
        address recipient,
        IERC2612 token,
        uint256 amount,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) internal {
        token.permit(_msgSender(), address(this), amount, deadline, v, r, s);
        token.safeTransferFrom(_msgSender(), recipient, amount);
        if (token.allowance(_msgSender(), address(this)) != 0) {
            revert ConfusedDeputy();
        }
    }
}
