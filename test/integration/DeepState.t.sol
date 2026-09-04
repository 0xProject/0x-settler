// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";

import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {RobinHoodSettler} from "src/chains/RobinHood/TakerSubmitted.sol";
import {ROBINHOOD_DEEPSTATE} from "src/core/Deepstate.sol";

import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";

interface IDeepstateV1Fork {
    function feeConfig() external view returns (address recipient, uint16 bps);
    function roots(address token0, address token1, uint256 epoch)
        external
        view
        returns (bytes32 askRoot, bytes32 bidRoot);
}

/// @dev Trades against the resting USDG/NVDA liquidity on the Deepstate engine at the fork block. USDG is
/// `token0`, so selling it is an ask and buying it is a bid. At block 53,608,000 the best bid is 75,796.31 USDG
/// at tick 716188984 and the best ask is 10,000 USDG at tick 716289359, with a 10 bps protocol fee.
contract DeepstateTest is SettlerBasePairTest {
    uint256 private constant BASIS = 1_000_000;
    IDeepstateV1Fork private constant DEEPSTATE = IDeepstateV1Fork(address(ROBINHOOD_DEEPSTATE));

    int32 private constant BEST_BID_TICK = 716_188_984;
    int32 private constant BEST_ASK_TICK = 716_289_359;
    // `floor(2**128 / price(BEST_ASK_TICK + 1))`: one tick past the limit so the engine's per-order round-up
    // cannot push the debit above the sell amount.
    uint256 private constant BEST_ASK_INVERSE_PRICE_X128 = 78_103_310_434_117_611_415_401_968_284;

    // The engine's quote for 1,000 USDG at the best bid before the fee, one wei above the ideal
    // `1e9 * price(BEST_BID_TICK)` because of its Q128 price factor rounding.
    uint256 private constant ASK_GROSS_OUT = 4_343_294_062_042_169_240;
    // 1 NVDA buys `1e18 * BEST_ASK_INVERSE_PRICE_X128 >> 128` USDG from the best ask.
    uint256 private constant BID_SELL_AMOUNT = 1 ether;
    uint256 private constant BID_GROSS_OUT = 229_525_000;

    function _testName() internal pure override returns (string memory) {
        return "USDG-NVDA";
    }

    function _testBlockNumber() internal pure override returns (uint256) {
        return 53_608_000;
    }

    function _testChainId() internal pure override returns (string memory) {
        return "robinhood";
    }

    function settlerInitCode() internal override returns (bytes memory) {
        return bytes.concat(type(RobinHoodSettler).creationCode, abi.encode(bytes20(0)));
    }

    function fromToken() internal pure override returns (IERC20) {
        return IERC20(0x5fc5360D0400a0Fd4f2af552ADD042D716F1d168); // USDG
    }

    function toToken() internal pure override returns (IERC20) {
        return IERC20(0xd0601CE157Db5bdC3162BbaC2a2C8aF5320D9EEC); // NVDA
    }

    function amount() internal pure override returns (uint256) {
        return 1_000e6;
    }

    function setUp() public override {
        super.setUp();
        vm.label(address(DEEPSTATE), "Deepstate");
        // The shared test key has an EIP-7702 delegation on Robinhood Chain, which makes Permit2 treat it as a
        // contract signer. Clear it so the taker signs as an EOA.
        vm.etch(FROM, new bytes(0));
        vm.makePersistent(FROM);
        safeApproveIfBelow(fromToken(), FROM, address(PERMIT2), amount());
        safeApproveIfBelow(toToken(), FROM, address(PERMIT2), BID_SELL_AMOUNT);
        (, uint16 feeBps) = DEEPSTATE.feeConfig();
        assertEq(feeBps, 10, "protocol fee changed");
    }

    function testDeepstate_ask() public {
        uint256 expectedOut = _netOfFee(ASK_GROSS_OUT);
        uint256 engineBalanceBefore = fromToken().balanceOf(address(DEEPSTATE));

        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(
                ISettlerActions.DEEPSTATE, (address(fromToken()), BASIS, address(toToken()), 0, BEST_BID_TICK, 0)
            )
        );
        ISettlerBase.AllowedSlippage memory slippage =
            ISettlerBase.AllowedSlippage({recipient: FROM, buyToken: toToken(), minAmountOut: expectedOut});

        vm.startPrank(FROM, FROM);
        snapStartName("settler_deepstate");
        settler.execute(slippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        assertEq(toToken().balanceOf(FROM), expectedOut, "taker output");
        assertEq(fromToken().balanceOf(address(DEEPSTATE)) - engineBalanceBefore, amount(), "engine received input");
        assertEq(fromToken().balanceOf(address(settler)), 0, "input fully matched");
        assertEq(toToken().balanceOf(address(settler)), 0, "settler output residue");
    }

    /// @dev The engine sizes bids in USDG, so the NVDA sell amount is converted through the inverse of the limit
    /// price. Everything matches at the best ask, which is one tick under the sizing price, so a sliver of NVDA
    /// is left unspent in the Settler.
    function testDeepstate_bid() public {
        uint256 expectedOut = _netOfFee(BID_GROSS_OUT);
        uint256 engineBalanceBefore = toToken().balanceOf(address(DEEPSTATE));

        deal(address(toToken()), FROM, BID_SELL_AMOUNT);
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) =
            _getDefaultFromPermit2(toToken(), BID_SELL_AMOUNT);
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(
                ISettlerActions.DEEPSTATE,
                (address(toToken()), BASIS, address(fromToken()), 0, BEST_ASK_TICK, BEST_ASK_INVERSE_PRICE_X128)
            )
        );
        ISettlerBase.AllowedSlippage memory slippage =
            ISettlerBase.AllowedSlippage({recipient: FROM, buyToken: fromToken(), minAmountOut: expectedOut});

        vm.startPrank(FROM, FROM);
        snapStartName("settler_deepstate_bid");
        settler.execute(slippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        uint256 spent = toToken().balanceOf(address(DEEPSTATE)) - engineBalanceBefore;
        assertEq(fromToken().balanceOf(FROM) - amount(), expectedOut, "taker output");
        assertEq(spent + toToken().balanceOf(address(settler)), BID_SELL_AMOUNT, "sell amount accounted for");
        assertLe(BID_SELL_AMOUNT - spent, BID_SELL_AMOUNT / 1e6, "unspent sliver above one tick of price");
        assertEq(fromToken().balanceOf(address(settler)), 0, "settler output residue");
    }

    function _netOfFee(uint256 grossOut) private pure returns (uint256) {
        return grossOut - grossOut * 10 / 10_000;
    }
}
