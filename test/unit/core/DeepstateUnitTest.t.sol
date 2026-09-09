// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {Test, stdError} from "@forge-std/Test.sol";
import {ERC20} from "@solmate/tokens/ERC20.sol";

import {ISettlerActions} from "src/ISettlerActions.sol";
import {BaseSettler} from "src/chains/Base/TakerSubmitted.sol";
import {RobinHoodSettler} from "src/chains/RobinHood/TakerSubmitted.sol";
import {Deepstate, ROBINHOOD_DEEPSTATE} from "src/core/Deepstate.sol";
import {Permit2PaymentTakerSubmitted} from "src/core/Permit2Payment.sol";
import {Permit2PaymentAbstract} from "src/core/Permit2PaymentAbstract.sol";
import {
    ActionInvalid,
    ConfusedDeputy,
    InvalidDeepstateRoute,
    NonStandardDeepstateToken,
    TooMuchSlippage
} from "src/core/SettlerErrors.sol";
import {IDeepstateV1} from "src/interfaces/IDeepstateV1.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {uint512} from "src/utils/512Math.sol";

contract DeepstateTestERC20 is ERC20 {
    constructor(string memory name_, string memory symbol_) ERC20(name_, symbol_, 18) {}

    function mint(address to, uint256 amount) external {
        _mint(to, amount);
    }
}

contract DeepstateFeeOnTransferToken is DeepstateTestERC20 {
    constructor() DeepstateTestERC20("Fee token", "FEE") {}

    function transferFrom(address from, address to, uint256 amount) public override returns (bool) {
        bool success = super.transferFrom(from, to, amount);
        if (amount != 0) _burn(to, 1);
        return success;
    }
}

contract DeepstatePoolMock is IDeepstateV1 {
    error FillFailed();

    IERC20 public inputToken;
    IERC20 public outputToken;
    IERC20 public unrelatedToken;
    uint256 public inputAmount;
    uint256 public outputAmount;
    uint256 public observedInputAllowance;
    uint256 public observedUnrelatedAllowance;
    uint256 public receivedValue;
    uint256 public callCount;
    address public observedToken0;
    address public observedToken1;
    uint256 public observedEpoch;
    bytes32 public observedOrder;
    bool public observedIsBid;
    bool public observedNoRest;
    bool public observedFillOrKill;
    bool public shouldRevert;

    function configure(IERC20 inputToken_, IERC20 outputToken_, uint256 inputAmount_, uint256 outputAmount_) external {
        inputToken = inputToken_;
        outputToken = outputToken_;
        inputAmount = inputAmount_;
        outputAmount = outputAmount_;
    }

    function observeUnrelatedToken(IERC20 token) external {
        unrelatedToken = token;
    }

    function setShouldRevert(bool value) external {
        shouldRevert = value;
    }

    function fill(FillParams calldata params) external payable returns (bytes32 restingOrder) {
        if (shouldRevert) revert FillFailed();

        ++callCount;
        receivedValue = msg.value;
        observedToken0 = params.token0;
        observedToken1 = params.token1;
        observedEpoch = params.epoch;
        observedOrder = params.order;
        observedIsBid = params.isBid;
        observedNoRest = params.noRest;
        observedFillOrKill = params.fillOrKill;

        if (address(inputToken) == address(0)) {
            if (inputAmount < msg.value) payable(msg.sender).transfer(msg.value - inputAmount);
        } else {
            observedInputAllowance = inputToken.allowance(msg.sender, address(this));
            if (address(unrelatedToken) != address(0)) {
                observedUnrelatedAllowance = unrelatedToken.allowance(msg.sender, address(this));
            }
            if (inputAmount != 0) require(inputToken.transferFrom(msg.sender, address(this), inputAmount));
        }

        if (outputAmount != 0) {
            if (address(outputToken) == address(0)) {
                payable(msg.sender).transfer(outputAmount);
            } else {
                require(outputToken.transfer(msg.sender, outputAmount));
            }
        }
        return bytes32(0);
    }

    receive() external payable {}
}

contract DeepstateDummy is Permit2PaymentTakerSubmitted, Deepstate {
    receive() external payable {}

    function sell(IERC20 sellToken, uint256 ppm, IERC20 buyToken, uint256 epoch, int32 tick, uint256 inversePriceX128)
        external
        payable
    {
        sellToDeepstate(sellToken, ppm, buyToken, epoch, tick, inversePriceX128);
    }

    function _tokenId() internal pure override returns (uint256) {
        revert("unimplemented");
    }

    function _hasMetaTxn() internal pure override returns (bool) {
        return false;
    }

    function _div512to256(uint512 n, uint512 d) internal view override returns (uint256) {
        return n.div(d);
    }

    function _dispatch(uint256, uint256, bytes calldata, ISettlerBase.AllowedSlippage memory)
        internal
        pure
        override
        returns (bool)
    {
        return false;
    }

    function _isRestrictedTarget(address target)
        internal
        view
        override(Deepstate, Permit2PaymentTakerSubmitted)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }
}

contract DeepstateUnitTest is Test {
    IERC20 private constant ETH_ADDRESS = IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE);
    uint256 private constant BASIS = 1_000_000;
    uint256 private constant Q128 = 1 << 128;

    DeepstateDummy private settler;
    DeepstatePoolMock private deepstate;
    DeepstateTestERC20 private token0;
    DeepstateTestERC20 private token1;
    DeepstateTestERC20 private unrelatedToken;
    address payable private receiver = payable(address(0xBEEF));

    function setUp() public {
        settler = new DeepstateDummy();
        DeepstatePoolMock implementation = new DeepstatePoolMock();
        vm.etch(address(ROBINHOOD_DEEPSTATE), address(implementation).code);
        deepstate = DeepstatePoolMock(payable(address(ROBINHOOD_DEEPSTATE)));

        DeepstateTestERC20 first = new DeepstateTestERC20("Token A", "A");
        DeepstateTestERC20 second = new DeepstateTestERC20("Token B", "B");
        (token0, token1) = address(first) < address(second) ? (first, second) : (second, first);
        unrelatedToken = new DeepstateTestERC20("Other", "OTHER");
    }

    function test_Deepstate_AskResizesFromBalanceAndLeavesRemainderForLaterActions() public {
        token0.mint(address(settler), 100);
        token1.mint(address(deepstate), 25);
        deepstate.configure(IERC20(address(token0)), IERC20(address(token1)), 50, 25);
        deepstate.observeUnrelatedToken(IERC20(address(unrelatedToken)));

        settler.sell(IERC20(address(token0)), 600_000, IERC20(address(token1)), 7, -123, 0);

        assertEq(deepstate.observedToken0(), address(token0));
        assertEq(deepstate.observedToken1(), address(token1));
        assertEq(deepstate.observedEpoch(), 7);
        assertEq(_tick(deepstate.observedOrder()), -123);
        assertEq(_quantity(deepstate.observedOrder()), 60);
        assertFalse(deepstate.observedIsBid());
        assertTrue(deepstate.observedNoRest());
        assertFalse(deepstate.observedFillOrKill());
        assertEq(deepstate.observedInputAllowance(), 60);
        assertEq(deepstate.observedUnrelatedAllowance(), 0);
        assertEq(token0.balanceOf(address(settler)), 50);
        assertEq(token0.balanceOf(address(deepstate)), 50);
        assertEq(token1.balanceOf(address(settler)), 25);
        assertEq(token0.allowance(address(settler), address(deepstate)), 0);
    }

    function testFuzz_Deepstate_AskResizesFromCurrentERC20Balance(uint128 balance, uint32 rawPpm) public {
        uint256 ppm = bound(rawPpm, 0, BASIS);
        uint256 expectedSellAmount = uint256(balance) * ppm / BASIS;
        token0.mint(address(settler), balance);
        deepstate.configure(IERC20(address(token0)), IERC20(address(token1)), expectedSellAmount, 0);

        settler.sell(IERC20(address(token0)), ppm, IERC20(address(token1)), 0, 0, 0);

        assertEq(_quantity(deepstate.observedOrder()), expectedSellAmount);
        assertEq(deepstate.observedInputAllowance(), expectedSellAmount);
        assertEq(token0.balanceOf(address(deepstate)), expectedSellAmount);
        assertEq(token0.balanceOf(address(settler)), uint256(balance) - expectedSellAmount);
        assertEq(token0.allowance(address(settler), address(deepstate)), 0);
    }

    function test_Deepstate_BidResizesQuoteBudgetThroughConservativeInversePrice() public {
        token1.mint(address(settler), 1_000);
        token0.mint(address(deepstate), 375);
        deepstate.configure(IERC20(address(token1)), IERC20(address(token0)), 750, 375);

        settler.sell(IERC20(address(token1)), 800_000, IERC20(address(token0)), 3, 99, Q128 / 2);

        assertEq(_quantity(deepstate.observedOrder()), 400);
        assertEq(_tick(deepstate.observedOrder()), 99);
        assertTrue(deepstate.observedIsBid());
        assertTrue(deepstate.observedNoRest());
        assertEq(deepstate.observedInputAllowance(), 800);
        assertEq(token1.balanceOf(address(settler)), 250);
        assertEq(token0.balanceOf(address(settler)), 375);
        assertEq(token1.allowance(address(settler), address(deepstate)), 0);
    }

    function testFuzz_Deepstate_BidResizesCurrentBalance(uint128 balance, uint128 inversePriceX128, uint32 rawPpm)
        public
    {
        uint256 ppm = bound(rawPpm, 0, BASIS);
        uint256 selectedBudget = uint256(balance) * ppm / BASIS;
        uint256 expectedQuantity = selectedBudget * inversePriceX128 >> 128;
        token1.mint(address(settler), balance);
        deepstate.configure(IERC20(address(token1)), IERC20(address(token0)), 0, 0);

        settler.sell(IERC20(address(token1)), ppm, IERC20(address(token0)), 0, 0, uint256(inversePriceX128));

        assertEq(_quantity(deepstate.observedOrder()), expectedQuantity);
        assertEq(deepstate.observedInputAllowance(), selectedBudget);
        assertEq(token1.balanceOf(address(settler)), balance);
        assertEq(token1.allowance(address(settler), address(deepstate)), 0);
    }

    function test_Deepstate_ExactAllowanceCapsBidAtPpmBudget() public {
        token1.mint(address(settler), 100);
        deepstate.configure(IERC20(address(token1)), IERC20(address(token0)), 51, 0);

        vm.expectRevert();
        settler.sell(IERC20(address(token1)), 500_000, IERC20(address(token0)), 0, 0, Q128);

        assertEq(token1.balanceOf(address(settler)), 100);
        assertEq(token1.balanceOf(address(deepstate)), 0);
        assertEq(token1.allowance(address(settler), address(deepstate)), 0);
        assertEq(deepstate.callCount(), 0);
    }

    function test_Deepstate_SaturatesAskQuantityWithoutCorruptingTick() public {
        token0.mint(address(settler), type(uint256).max);
        deepstate.configure(IERC20(address(token0)), IERC20(address(token1)), 0, 0);

        settler.sell(IERC20(address(token0)), BASIS, IERC20(address(token1)), 0, type(int32).min, 0);

        assertEq(_quantity(deepstate.observedOrder()), type(uint160).max);
        assertEq(_tick(deepstate.observedOrder()), type(int32).min);
        assertEq(deepstate.observedInputAllowance(), type(uint256).max);
        assertEq(token0.allowance(address(settler), address(deepstate)), 0);
    }

    function test_Deepstate_SaturatesOverflowingBidQuantity() public {
        token1.mint(address(settler), type(uint256).max);
        deepstate.configure(IERC20(address(token1)), IERC20(address(token0)), 0, 0);

        settler.sell(IERC20(address(token1)), BASIS, IERC20(address(token0)), 0, type(int32).max, type(uint256).max);

        assertEq(_quantity(deepstate.observedOrder()), type(uint160).max);
        assertEq(_tick(deepstate.observedOrder()), type(int32).max);
        assertEq(deepstate.observedInputAllowance(), type(uint256).max);
        assertEq(token1.allowance(address(settler), address(deepstate)), 0);
    }

    function test_Deepstate_RejectsInexactInputSettlement() public {
        DeepstateFeeOnTransferToken feeToken = new DeepstateFeeOnTransferToken();
        feeToken.mint(address(settler), 100);
        IERC20 feeAsset = IERC20(address(feeToken));
        IERC20 outputAsset = address(feeToken) < address(token0) ? IERC20(address(token0)) : ETH_ADDRESS;
        deepstate.configure(feeAsset, IERC20(address(token0)), 100, 0);

        vm.expectRevert(abi.encodeWithSelector(NonStandardDeepstateToken.selector, address(feeToken)));
        settler.sell(feeAsset, BASIS, outputAsset, 0, 0, Q128);

        assertEq(feeToken.balanceOf(address(settler)), 100);
        assertEq(feeToken.balanceOf(address(deepstate)), 0);
    }

    function test_Deepstate_NativeAskForwardsOnlySelectedBudgetAndKeepsRefund() public {
        vm.deal(address(settler), 10 ether);
        deepstate.configure(IERC20(address(0)), IERC20(address(token1)), 4 ether, 0);

        settler.sell(ETH_ADDRESS, 600_000, IERC20(address(token1)), 0, 0, 0);

        assertEq(deepstate.receivedValue(), 6 ether);
        assertEq(_quantity(deepstate.observedOrder()), 6 ether);
        assertTrue(deepstate.observedNoRest());
        assertEq(address(settler).balance, 6 ether);
        assertEq(address(deepstate).balance, 4 ether);
    }

    function test_Deepstate_ERC20FillDoesNotForwardUnrelatedNativeBalance() public {
        vm.deal(address(settler), 10 ether);
        token0.mint(address(settler), 100);
        deepstate.configure(IERC20(address(token0)), IERC20(address(token1)), 100, 0);

        settler.sell(IERC20(address(token0)), BASIS, IERC20(address(token1)), 0, 0, 0);

        assertEq(deepstate.receivedValue(), 0);
        assertEq(address(settler).balance, 10 ether);
        assertEq(address(deepstate).balance, 0);
    }

    function test_Deepstate_RevertIsAtomic() public {
        token0.mint(address(settler), 100);
        deepstate.configure(IERC20(address(token0)), IERC20(address(token1)), 60, 0);
        deepstate.setShouldRevert(true);

        vm.expectRevert(DeepstatePoolMock.FillFailed.selector);
        settler.sell(IERC20(address(token0)), 600_000, IERC20(address(token1)), 0, 0, 0);

        assertEq(token0.balanceOf(address(settler)), 100);
        assertEq(token0.balanceOf(address(deepstate)), 0);
        assertEq(token0.allowance(address(settler), address(deepstate)), 0);
    }

    function test_Deepstate_RejectsInvalidAssets() public {
        vm.expectRevert(InvalidDeepstateRoute.selector);
        settler.sell(IERC20(address(token0)), BASIS, IERC20(address(token0)), 0, 0, 0);

        vm.expectRevert(InvalidDeepstateRoute.selector);
        settler.sell(IERC20(address(0)), BASIS, IERC20(address(token1)), 0, 0, 0);

        vm.expectRevert(InvalidDeepstateRoute.selector);
        settler.sell(IERC20(address(token0)), BASIS, IERC20(address(0)), 0, 0, 0);
    }

    function test_Deepstate_ActionEncodingUsesBalanceSizedABI() public pure {
        bytes memory action = abi.encodeCall(
            ISettlerActions.DEEPSTATE, (address(ETH_ADDRESS), BASIS, address(0xCAFE), 7, int32(-123), Q128)
        );

        assertEq(bytes4(action), ISettlerActions.DEEPSTATE.selector);
        assertEq(address(ROBINHOOD_DEEPSTATE), 0x6cf19308C22FC82ea620Fa0B3E94948d20f27B96);
    }

    function test_Deepstate_DeploymentRequiresEngineCode() public {
        vm.chainId(4663);
        vm.etch(address(ROBINHOOD_DEEPSTATE), bytes(""));

        vm.expectRevert(stdError.assertionError);
        new DeepstateDummy();
    }

    function test_Deepstate_EngineIsRestrictedFromBasicAction() public {
        RobinHoodSettler deployedSettler = _deploySettler();
        bytes[] memory actions = new bytes[](1);
        actions[0] =
            abi.encodeCall(ISettlerActions.BASIC, (address(token0), BASIS, address(ROBINHOOD_DEEPSTATE), 0, bytes("")));

        vm.expectRevert(ConfusedDeputy.selector);
        deployedSettler.execute(
            ISettlerBase.AllowedSlippage({recipient: receiver, buyToken: IERC20(address(0)), minAmountOut: 0}),
            actions,
            bytes32(0)
        );

        assertEq(deepstate.callCount(), 0);
        assertEq(token0.allowance(address(deployedSettler), address(deepstate)), 0);
    }

    function test_Deepstate_ActionDispatchesThroughRobinHoodSettler() public {
        RobinHoodSettler deployedSettler = _deploySettler();
        token0.mint(address(deployedSettler), 100);
        token1.mint(address(deepstate), 25);
        deepstate.configure(IERC20(address(token0)), IERC20(address(token1)), 60, 25);

        bytes[] memory actions = _action(address(token0), BASIS, address(token1), 0, 0, 0);
        deployedSettler.execute(
            ISettlerBase.AllowedSlippage({recipient: receiver, buyToken: IERC20(address(token1)), minAmountOut: 25}),
            actions,
            bytes32(0)
        );

        assertTrue(deepstate.observedNoRest());
        assertEq(_quantity(deepstate.observedOrder()), 100);
        assertEq(token0.balanceOf(address(deployedSettler)), 40);
        assertEq(token0.balanceOf(address(deepstate)), 60);
        assertEq(token1.balanceOf(receiver), 25);
        assertEq(token0.allowance(address(deployedSettler), address(deepstate)), 0);
    }

    function test_Deepstate_ActionEnforcesTransactionSlippage() public {
        RobinHoodSettler deployedSettler = _deploySettler();
        token0.mint(address(deployedSettler), 100);
        token1.mint(address(deepstate), 24);
        deepstate.configure(IERC20(address(token0)), IERC20(address(token1)), 60, 24);

        bytes[] memory actions = _action(address(token0), BASIS, address(token1), 0, 0, 0);
        vm.expectRevert(abi.encodeWithSelector(TooMuchSlippage.selector, address(token1), 25, 24));
        deployedSettler.execute(
            ISettlerBase.AllowedSlippage({recipient: receiver, buyToken: IERC20(address(token1)), minAmountOut: 25}),
            actions,
            bytes32(0)
        );

        assertEq(token0.balanceOf(address(deployedSettler)), 100);
        assertEq(token0.balanceOf(address(deepstate)), 0);
        assertEq(token1.balanceOf(receiver), 0);
        assertEq(token0.allowance(address(deployedSettler), address(deepstate)), 0);
    }

    function test_Deepstate_BidCanPayOutNativeOutput() public {
        RobinHoodSettler deployedSettler = _deploySettler();
        token1.mint(address(deployedSettler), 100);
        vm.deal(address(deepstate), 25);
        deepstate.configure(IERC20(address(token1)), IERC20(address(0)), 60, 25);

        bytes[] memory actions = _action(address(token1), BASIS, address(ETH_ADDRESS), 0, 0, Q128);
        deployedSettler.execute(
            ISettlerBase.AllowedSlippage({recipient: receiver, buyToken: ETH_ADDRESS, minAmountOut: 25}),
            actions,
            bytes32(0)
        );

        assertTrue(deepstate.observedIsBid());
        assertEq(receiver.balance, 25);
        assertEq(token1.balanceOf(address(deployedSettler)), 40);
        assertEq(address(deployedSettler).balance, 0);
        assertEq(token1.allowance(address(deployedSettler), address(deepstate)), 0);
    }

    function test_Deepstate_ActionIsUnavailableOutsideRobinHood() public {
        BaseSettler baseSettler =
            BaseSettler(payable(deployCode("TakerSubmitted.sol:BaseSettler", abi.encode(bytes20(0)))));
        bytes memory actionData = abi.encode(address(token0), BASIS, address(token1), 0, int32(0), uint256(0));
        bytes[] memory actions = new bytes[](1);
        actions[0] = bytes.concat(ISettlerActions.DEEPSTATE.selector, actionData);

        vm.expectRevert(
            abi.encodeWithSelector(ActionInvalid.selector, 0, ISettlerActions.DEEPSTATE.selector, actionData)
        );
        baseSettler.execute(
            ISettlerBase.AllowedSlippage({recipient: receiver, buyToken: IERC20(address(token1)), minAmountOut: 0}),
            actions,
            bytes32(0)
        );
    }

    function _deploySettler() private returns (RobinHoodSettler deployedSettler) {
        deployedSettler =
            RobinHoodSettler(payable(deployCode("TakerSubmitted.sol:RobinHoodSettler", abi.encode(bytes20(0)))));
    }

    function _action(
        address sellToken,
        uint256 ppm,
        address buyToken,
        uint256 epoch,
        int32 tick,
        uint256 inversePriceX128
    ) private pure returns (bytes[] memory actions) {
        actions = new bytes[](1);
        actions[0] =
            abi.encodeCall(ISettlerActions.DEEPSTATE, (sellToken, ppm, buyToken, epoch, tick, inversePriceX128));
    }

    function _quantity(bytes32 order) private pure returns (uint160 quantity) {
        quantity = uint160(uint256(order >> 64));
    }

    function _tick(bytes32 order) private pure returns (int32 tick) {
        assembly ("memory-safe") {
            tick := signextend(3, shr(0xe0, order))
        }
    }
}
