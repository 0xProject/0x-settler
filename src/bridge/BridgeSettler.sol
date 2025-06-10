// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {BridgeSettlerBase} from "./BridgeSettlerBase.sol";
import {revertActionInvalid} from "../core/SettlerErrors.sol";
import {CalldataDecoder} from "../SettlerBase.sol";
import {UnsafeMath} from "../utils/UnsafeMath.sol";

interface IBridgeSettlerTakerSubmitted {
    function execute(bytes[] calldata, bytes32)
        external
        payable
        returns (bool);
}

abstract contract BridgeSettler is IBridgeSettlerTakerSubmitted, BridgeSettlerBase {
    using CalldataDecoder for bytes[];
    using UnsafeMath for uint256;

    function _tokenId() internal pure override returns (uint256) {
        return 5;
    }

    function execute(bytes[] calldata actions, bytes32 /* zid & affiliate */ )
        public
        payable
        override
        returns (bool)
    {
        for (uint256 i = 0; i < actions.length; i = i.unsafeInc()) {
            (uint256 action, bytes calldata data) = actions.decodeCall(i);
            if (!_dispatch(i, action, data)) {
                revertActionInvalid(i, action, data);
            }
        }

        return true;
    }
}