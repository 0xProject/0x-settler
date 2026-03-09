// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {BaseSettler} from "src/chains/Base/TakerSubmitted.sol";
import {BaseSettlerMetaTxn} from "src/chains/Base/MetaTxn.sol";
import {BaseSettlerIntent} from "src/chains/Base/Intent.sol";

interface IRebateClaimer {
    function rebateClaimer() external view returns (address);
}

contract RebateClaimerUnitTest is Test {
    address private constant EXPECTED_REBATE_CLAIMER = 0x352650Ac2653508d946c4912B07895B22edd84CD;

    BaseSettler internal settler;
    BaseSettlerMetaTxn internal settlerMetaTxn;
    BaseSettlerIntent internal settlerIntent;
    RebateClaimerCallbackHelper internal callbackHelper;

    function setUp() public {
        settler = BaseSettler(payable(deployCode("TakerSubmitted.sol:BaseSettler", abi.encode(bytes20(0)))));
        settlerMetaTxn =
            BaseSettlerMetaTxn(payable(deployCode("MetaTxn.sol:BaseSettlerMetaTxn", abi.encode(bytes20(0)))));
        settlerIntent = BaseSettlerIntent(payable(deployCode("Intent.sol:BaseSettlerIntent", abi.encode(bytes20(0)))));
        callbackHelper = new RebateClaimerCallbackHelper();
    }

    function test_rebateClaimer_TakerSubmitted_ReturnsConstant() public view {
        address claimer = IRebateClaimer(address(settler)).rebateClaimer();
        assertEq(claimer, EXPECTED_REBATE_CLAIMER, "rebateClaimer should return the constant address");
    }

    function test_rebateClaimer_MetaTxn_ReturnsConstant() public view {
        address claimer = IRebateClaimer(address(settlerMetaTxn)).rebateClaimer();
        assertEq(claimer, EXPECTED_REBATE_CLAIMER, "rebateClaimer should return the constant address");
    }

    function test_rebateClaimer_Intent_ReturnsConstant() public view {
        address claimer = IRebateClaimer(address(settlerIntent)).rebateClaimer();
        assertEq(claimer, EXPECTED_REBATE_CLAIMER, "rebateClaimer should return the constant address");
    }

    function test_rebateClaimer_ReturnsDuringExecution() public {
        address testPayer = makeAddr("testPayer");

        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(
            ISettlerActions.BASIC,
            (
                address(0),              // sellToken (no transfer needed)
                0,                       // bps
                address(callbackHelper), // pool
                0,                       // offset
                abi.encodeCall(RebateClaimerCallbackHelper.checkRebateClaimer, (address(settler)))
            )
        );

        vm.prank(testPayer, testPayer);
        settler.execute(
            ISettlerBase.AllowedSlippage({
                recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
            }),
            actions,
            bytes32(0)
        );

        assertEq(
            callbackHelper.lastRebateClaimer(),
            EXPECTED_REBATE_CLAIMER,
            "rebateClaimer should return constant during execution"
        );
    }
}

contract RebateClaimerCallbackHelper {
    address public lastRebateClaimer;

    function checkRebateClaimer(address settler) external {
        lastRebateClaimer = IRebateClaimer(settler).rebateClaimer();
    }
}
