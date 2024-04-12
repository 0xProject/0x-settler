// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {MultiCallBase} from "./MultiCall.sol";
import {AbstractUUPSUpgradeable} from "../proxy/ERC1967UUPSUpgradeable.sol";

abstract contract ProxyMultiCall is AbstractUUPSUpgradeable, MultiCallBase {
    function multicall(bytes[] calldata datas) external override {
        _multicall(_implementation, datas);
    }
}
