// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SettlerMetaTxnBase} from "./SettlerMetaTxnBase.sol";

abstract contract SettlerMetaTxn is SettlerMetaTxnBase {
    function _tokenId() internal pure override returns (uint256) {
        return 3;
    }

    function executeMetaTxn(
        AllowedSlippage calldata slippage,
        bytes[] calldata actions,
        bytes32, /* zid & affiliate */
        address msgSender,
        bytes calldata sig
    ) external metaTx(msgSender, _hashSlippageAnd(SLIPPAGE_AND_ACTIONS_TYPEHASH, actions, slippage)) returns (bool) {
        return _executeMetaTxn(slippage, actions, sig, 0);
    }

    function _witnessTypeSuffix() internal pure override returns (string memory) {
        return string(
            abi.encodePacked(
                "SlippageAndActions slippageAndActions)", SLIPPAGE_AND_ACTIONS_TYPE, TOKEN_PERMISSIONS_TYPE
            )
        );
    }
}
