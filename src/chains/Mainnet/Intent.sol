// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {SettlerIntent} from "../../SettlerIntent.sol";
import {MainnetSettlerMetaTxnBase} from "./MetaTxn.sol";
import {Chainlink} from "../../core/Chainlink.sol";

import {ISettlerActions} from "../../ISettlerActions.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";
import {SettlerBase} from "../../SettlerBase.sol";
import {SettlerMetaTxnBase} from "../../SettlerMetaTxn.sol";

/// @custom:security-contact security@0x.org
contract MainnetSettlerIntent is SettlerIntent, MainnetSettlerMetaTxnBase, Chainlink {
    constructor(bytes20 gitCommit) SettlerBase(gitCommit) {}

    function _dispatch(uint256 action, bytes calldata data)
        internal
        override(MainnetSettlerMetaTxnBase, SettlerBase, SettlerAbstract)
        returns (bool)
    {
        if (super._dispatch(action, data)) {
            return true;
        } else if (action == uint32(ISettlerActions.CHAINLINK.selector)) {
            (string memory feedName, int256 priceThreshold, uint8 expectedDecimals, uint256 staleThreshold) = abi.decode(data, (string, int256, uint8, uint256));

            consultChainlink(feedName, priceThreshold, expectedDecimals, staleThreshold);
        } else {
            return false;
        }
        return true;
    }

    // Solidity inheritance is stupid
    function _dispatchVIP(uint256 action, bytes calldata data, bytes calldata sig)
        internal
        override(MainnetSettlerMetaTxnBase, SettlerMetaTxnBase)
        returns (bool)
    {
        return super._dispatchVIP(action, data, sig);
    }
}
