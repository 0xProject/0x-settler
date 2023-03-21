// SPDX-License-Identifier: MIT
pragma solidity ^0.8.17;

import {BasePairTest} from "./BasePairTest.t.sol";

abstract contract CurveV2PairTest is BasePairTest {
    function getCurvePoolData() internal virtual returns (CurvePoolData memory);

    struct CurvePoolData {
        address pool;
        uint256 fromTokenIndex;
        uint256 toTokenIndex;
    }

    function testCurveV2() public {
    }
}
