// SPDX-License-Identifier: MIT
pragma solidity =0.8.25;

import {SettlerIntent} from "../../SettlerIntent.sol";
import {MainnetSettlerMetaTxnBase} from "./MetaTxn.sol";

// Solidity inheritance is stupid
import {SettlerAbstract} from "../../SettlerAbstract.sol";
import {SettlerBase} from "../../SettlerBase.sol";
import {SettlerMetaTxnBase} from "../../SettlerMetaTxn.sol";

/// @custom:security-contact security@0x.org
contract MainnetSettlerIntent is SettlerIntent, MainnetSettlerMetaTxnBase {
    constructor(bytes20 gitCommit) SettlerBase(gitCommit) {}

    // Solidity inheritance is stupid
    function _dispatch(uint256 action, bytes calldata data)
        internal
        override(MainnetSettlerMetaTxnBase, SettlerBase, SettlerAbstract)
        returns (bool)
    {
        return super._dispatch(action, data);
    }

    function _dispatchVIP(uint256 action, bytes calldata data, bytes calldata sig)
        internal
        override(MainnetSettlerMetaTxnBase, SettlerMetaTxnBase)
        returns (bool)
    {
        return super._dispatchVIP(action, data, sig);
    }
}
