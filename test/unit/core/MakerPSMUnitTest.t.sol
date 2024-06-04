// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {MakerPSM, IPSM} from "../../../src/core/MakerPSM.sol";

import {IERC20, IERC20Meta} from "../../../src/IERC20.sol";
import {Utils} from "../Utils.sol";

import {Test} from "forge-std/Test.sol";

contract MakerPSMDummy is MakerPSM {
    function sellToPool(address recipient, address gemToken, uint256 bps, address psm) public {
        super.sellToMakerPsm(recipient, IERC20Meta(gemToken), bps, IPSM(psm), false);
    }

    function buyFromPool(address recipient, address gemToken, uint256 bps, address psm) public {
        super.sellToMakerPsm(recipient, IERC20Meta(gemToken), bps, IPSM(psm), true);
    }
}

contract MakerPSMUnitTest is Utils, Test {
    MakerPSMDummy psm;
    address POOL = _createNamedRejectionDummy("POOL");
    address RECIPIENT = _createNamedRejectionDummy("RECIPIENT");
    address PSM = _createNamedRejectionDummy("PSM");
    address DAI = _etchNamedRejectionDummy("DAI", 0x6B175474E89094C44Da98b954EedeAC495271d0F);
    address TOKEN = _createNamedRejectionDummy("TOKEN");

    function setUp() public {
        psm = new MakerPSMDummy();
    }

    function testMakerPSMSell() public {
        uint256 bps = 10_000;
        uint256 amount = 99999;

        _mockExpectCall(TOKEN, abi.encodeWithSelector(IERC20.balanceOf.selector, address(psm)), abi.encode(amount));
        _mockExpectCall(TOKEN, abi.encodeWithSelector(IERC20.allowance.selector, address(psm), PSM), abi.encode(amount));
        _mockExpectCall(PSM, abi.encodeWithSelector(IPSM.gemJoin.selector), abi.encode(PSM));
        _mockExpectCall(PSM, abi.encodeWithSelector(IPSM.sellGem.selector, RECIPIENT, amount), abi.encode(true));

        psm.sellToPool(RECIPIENT, TOKEN, bps, PSM);
    }

    function testMakerPSMBuy() public {
        uint256 bps = 10_000;
        uint256 amount = 99999;

        _mockExpectCall(DAI, abi.encodeWithSelector(IERC20.balanceOf.selector, address(psm)), abi.encode(amount));
        _mockExpectCall(DAI, abi.encodeWithSelector(IERC20.allowance.selector, address(psm), PSM), abi.encode(amount));
        _mockExpectCall(TOKEN, abi.encodeWithSelector(IERC20Meta.decimals.selector), abi.encode(18));
        _mockExpectCall(PSM, abi.encodeWithSelector(IPSM.tout.selector), abi.encode(100));
        _mockExpectCall(PSM, abi.encodeWithSelector(IPSM.buyGem.selector, RECIPIENT, 99998), abi.encode(true));

        psm.buyFromPool(RECIPIENT, TOKEN, bps, PSM);
    }
}
