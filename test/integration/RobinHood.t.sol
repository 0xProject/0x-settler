// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {Test} from "@forge-std/Test.sol";
import {GasSnapshot} from "@forge-gas-snapshot/GasSnapshot.sol";
import {ERC20} from "@solmate/tokens/ERC20.sol";

import {ISettlerActions} from "src/ISettlerActions.sol";
import {RobinHoodSettler} from "src/chains/RobinHood/TakerSubmitted.sol";
import {ROBINHOOD_DEEPSTATE} from "src/core/Deepstate.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {IDeepstateV1} from "src/interfaces/IDeepstateV1.sol";

import {BebopPairTest} from "./BebopPairTest.t.sol";
import {BasePairTest} from "./BasePairTest.t.sol";
import {MainnetDefaultFork} from "./BaseForkTest.t.sol";
import {OrvexCLTest} from "./OrvexCL.t.sol";
import {PancakeInfinityTest} from "./PancakeInfinity.t.sol";
import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";

contract RobinHoodWETHNVDATest is BebopPairTest, OrvexCLTest {
    function setUp() public override(PancakeInfinityTest, BebopPairTest) {
        super.setUp();
    }

    function _testBlockNumber() internal pure override(MainnetDefaultFork, OrvexCLTest) returns (uint256) {
        return super._testBlockNumber();
    }

    function _testChainId() internal pure override(MainnetDefaultFork, OrvexCLTest) returns (string memory) {
        return super._testChainId();
    }

    function settlerInitCode() internal override(OrvexCLTest, SettlerBasePairTest) returns (bytes memory) {
        return super.settlerInitCode();
    }

    function sqrtPriceLimitX96(IERC20 sellToken, IERC20 buyToken)
        internal
        view
        override(BasePairTest, PancakeInfinityTest)
        returns (uint160)
    {
        return super.sqrtPriceLimitX96(sellToken, buyToken);
    }

    function pancakeInfinityForkName() internal pure override returns (string memory) {
        return "orvex";
    }

    function _testName() internal pure override returns (string memory) {
        return "WETH-NVDA";
    }

    function fromToken() internal pure override returns (IERC20) {
        return IERC20(0x0Bd7D308f8E1639FAb988df18A8011f41EAcAD73); // WETH
    }

    function toToken() internal pure override returns (IERC20) {
        return IERC20(0xd0601CE157Db5bdC3162BbaC2a2C8aF5320D9EEC); // NVDA
    }

    function poolId() internal view virtual override returns (bytes32) {
        return bytes32(0x257df135116403937e4b04b22b796e6746d965090fef574b684c9c294c542490);
    }

    function amount() internal view virtual override returns (uint256) {
        return 0.1 ether;
    }
}

interface IDeepstateV1Fork is IDeepstateV1 {
    function feeConfig() external view returns (address recipient, uint16 bps);
    function roots(address token0, address token1, uint256 epoch)
        external
        view
        returns (bytes32 askRoot, bytes32 bidRoot);
}

contract DeepstateLiveTestToken is ERC20 {
    constructor(string memory name_, string memory symbol_) ERC20(name_, symbol_, 18) {}

    function mint(address to, uint256 amount) external {
        _mint(to, amount);
    }
}

contract DeepstateRobinHoodTest is Test, GasSnapshot {
    uint256 private constant FORK_BLOCK = 52_936_000;
    uint256 private constant BASIS = 1_000_000;
    uint160 private constant MAKER_QUANTITY = 100 ether;
    uint160 private constant TAKER_QUANTITY = 120 ether;
    int32 private constant PRICE_EIGHT_TICK = 1 << 26;
    uint256 private constant INVERSE_PRICE_EIGHT_X128 = 1 << 125;
    IDeepstateV1Fork private constant DEEPSTATE = IDeepstateV1Fork(address(ROBINHOOD_DEEPSTATE));

    RobinHoodSettler private settler;
    DeepstateLiveTestToken private token0;
    DeepstateLiveTestToken private token1;
    address private maker = address(0xA11CE);
    address payable private receiver = payable(address(0xBEEF));
    uint16 private protocolFeeBps;

    function setUp() public {
        vm.createSelectFork("robinhood", FORK_BLOCK);
        assertEq(block.chainid, 4663, "fork must be Robinhood Chain");
        assertGt(address(DEEPSTATE).code.length, 0, "live engine missing");

        // RobinHoodSettler has no immutable or constructor-initialized state.
        settler = RobinHoodSettler(payable(address(0x5E771E7)));
        vm.etch(address(settler), vm.getDeployedCode("TakerSubmitted.sol:RobinHoodSettler"));

        DeepstateLiveTestToken first = new DeepstateLiveTestToken("Deepstate 0x A", "DS0A");
        DeepstateLiveTestToken second = new DeepstateLiveTestToken("Deepstate 0x B", "DS0B");
        (token0, token1) = address(first) < address(second) ? (first, second) : (second, first);

        (address feeRecipient, uint16 feeBps) = DEEPSTATE.feeConfig();
        assertTrue(feeRecipient != address(0), "protocol fee recipient missing");
        assertEq(feeBps, 10, "unexpected live protocol fee");
        protocolFeeBps = feeBps;

        token1.mint(maker, MAKER_QUANTITY);
        vm.startPrank(maker);
        token1.approve(address(DEEPSTATE), MAKER_QUANTITY);
        bytes32 restingOrder = DEEPSTATE.fill(_fill(MAKER_QUANTITY, true, false, 0));
        vm.stopPrank();
        assertTrue(restingOrder != bytes32(0), "maker bid did not rest");
    }

    function test_Deepstate_AskResizesThroughSettlerAgainstLiveEngine() public {
        token0.mint(address(settler), TAKER_QUANTITY);

        uint256 expectedOut = MAKER_QUANTITY - MAKER_QUANTITY * protocolFeeBps / 10_000;
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(ISettlerActions.DEEPSTATE, (address(token0), BASIS, address(token1), 0, 0, 0));
        snapStart("settler_deepstate_robinhood");
        settler.execute(
            ISettlerBase.AllowedSlippage({
                recipient: receiver, buyToken: IERC20(address(token1)), minAmountOut: expectedOut
            }),
            actions,
            bytes32(0)
        );
        snapEnd();

        assertEq(token1.balanceOf(receiver), expectedOut, "receiver output");
        assertEq(token0.balanceOf(address(DEEPSTATE)), MAKER_QUANTITY, "engine input settlement");
        assertEq(token0.balanceOf(address(settler)), TAKER_QUANTITY - MAKER_QUANTITY, "unmatched input remainder");
        assertEq(token1.balanceOf(address(settler)), 0, "settler output residue");
        assertEq(token0.allowance(address(settler), address(DEEPSTATE)), 0, "temporary allowance");

        (bytes32 askRoot, bytes32 bidRoot) = DEEPSTATE.roots(address(token0), address(token1), 0);
        assertEq(askRoot, bytes32(0), "unmatched ask rested");
        assertEq(bidRoot, bytes32(0), "maker bid not consumed");
    }

    function test_Deepstate_BidResizesPpmBudgetAtNonzeroTickWithoutResting() public {
        uint160 eachMakerQuantity = 60 ether;
        uint160 totalMakerQuantity = eachMakerQuantity * 2;
        token0.mint(maker, totalMakerQuantity);
        vm.startPrank(maker);
        token0.approve(address(DEEPSTATE), totalMakerQuantity);
        assertTrue(DEEPSTATE.fill(_fill(eachMakerQuantity, false, false, PRICE_EIGHT_TICK)) != bytes32(0));
        assertTrue(DEEPSTATE.fill(_fill(eachMakerQuantity, false, false, PRICE_EIGHT_TICK)) != bytes32(0));
        vm.stopPrank();

        (bytes32 askRootBefore, bytes32 bidRootBefore) = DEEPSTATE.roots(address(token0), address(token1), 0);
        assertTrue(askRootBefore != bytes32(0), "maker asks did not rest");
        assertTrue(bidRootBefore != bytes32(0), "existing maker bid missing");

        uint256 sellBalance = 2_000 ether;
        uint256 selectedBudget = sellBalance / 2;
        uint256 spent = uint256(totalMakerQuantity) * 8;
        token1.mint(address(settler), sellBalance);

        uint256 expectedOut = totalMakerQuantity - uint256(totalMakerQuantity) * protocolFeeBps / 10_000;
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(
            ISettlerActions.DEEPSTATE,
            (address(token1), BASIS / 2, address(token0), 0, PRICE_EIGHT_TICK, INVERSE_PRICE_EIGHT_X128)
        );
        settler.execute(
            ISettlerBase.AllowedSlippage({
                recipient: receiver, buyToken: IERC20(address(token0)), minAmountOut: expectedOut
            }),
            actions,
            bytes32(0)
        );

        assertEq(token0.balanceOf(receiver), expectedOut, "receiver output");
        assertEq(token1.balanceOf(address(settler)), sellBalance - spent, "unused input remainder");
        assertEq(token0.balanceOf(address(settler)), 0, "settler output residue");
        assertEq(token1.allowance(address(settler), address(DEEPSTATE)), 0, "temporary allowance");
        assertGt(selectedBudget, spent, "test requires an unmatched bid remainder");

        (bytes32 askRootAfter, bytes32 bidRootAfter) = DEEPSTATE.roots(address(token0), address(token1), 0);
        assertEq(askRootAfter, bytes32(0), "maker asks not consumed");
        assertEq(bidRootAfter, bidRootBefore, "unmatched bid rested");
    }

    function _fill(uint160 quantity, bool isBid, bool noRest, int32 tick)
        private
        view
        returns (IDeepstateV1.FillParams memory params)
    {
        params = IDeepstateV1.FillParams({
            token0: address(token0),
            token1: address(token1),
            epoch: 0,
            order: bytes32((uint256(uint32(tick)) << 224) | (uint256(quantity) << 64)),
            isBid: isBid,
            noRest: noRest,
            fillOrKill: false
        });
    }
}
