// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {Test, stdError} from "@forge-std/Test.sol";
import {ERC20} from "@solmate/tokens/ERC20.sol";

import {ISettlerActions} from "src/ISettlerActions.sol";
import {BaseSettler} from "src/chains/Base/TakerSubmitted.sol";
import {RobinHoodSettler} from "src/chains/RobinHood/TakerSubmitted.sol";
import {Permit2PaymentTakerSubmitted} from "src/core/Permit2Payment.sol";
import {Permit2PaymentAbstract} from "src/core/Permit2PaymentAbstract.sol";
import {Deepstate, ROBINHOOD_DEEPSTATE} from "src/core/Deepstate.sol";
import {
    ActionInvalid,
    ConfusedDeputy,
    InvalidDeepstateRoute,
    NonStandardDeepstateToken,
    TooMuchSlippage
} from "src/core/SettlerErrors.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {IDeepstateV1} from "src/interfaces/IDeepstateV1.sol";
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
    bool public allNoRest;
    bool public lastFillOrKill;
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

    function fillRoute(FillParams[] calldata fills) external payable {
        if (shouldRevert) revert FillFailed();

        ++callCount;
        receivedValue = msg.value;
        allNoRest = true;

        for (uint256 i; i < fills.length;) {
            allNoRest = allNoRest && fills[i].noRest;
            lastFillOrKill = fills[i].fillOrKill;
            unchecked {
                ++i;
            }
        }

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
    }

    receive() external payable {}
}

contract DeepstateDummy is Permit2PaymentTakerSubmitted, Deepstate {
    receive() external payable {}

    function sell(
        address payable recipient,
        IERC20 sellToken,
        IERC20 buyToken,
        uint256 ppm,
        IDeepstateV1.FillParams[] memory fills
    ) external payable {
        sellToDeepstate(recipient, sellToken, buyToken, ppm, fills);
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

    DeepstateDummy private settler;
    DeepstatePoolMock private deepstate;
    DeepstateTestERC20 private sellToken;
    DeepstateTestERC20 private buyToken;
    DeepstateTestERC20 private unrelatedToken;
    IERC20 private sellAsset;
    IERC20 private buyAsset;
    address payable private receiver = payable(address(0xBEEF));

    function setUp() public {
        settler = new DeepstateDummy();
        DeepstatePoolMock implementation = new DeepstatePoolMock();
        vm.etch(address(ROBINHOOD_DEEPSTATE), address(implementation).code);
        deepstate = DeepstatePoolMock(payable(address(ROBINHOOD_DEEPSTATE)));
        sellToken = new DeepstateTestERC20("Sell token", "SELL");
        buyToken = new DeepstateTestERC20("Buy token", "BUY");
        unrelatedToken = new DeepstateTestERC20("Unrelated token", "OTHER");
        sellAsset = IERC20(address(sellToken));
        buyAsset = IERC20(address(buyToken));
    }

    function test_Deepstate_BoundsSpendAndRefundsOnlySelectedRemainder() public {
        sellToken.mint(address(settler), 100);
        buyToken.mint(address(deepstate), 25);
        deepstate.configure(IERC20(address(sellToken)), IERC20(address(buyToken)), 50, 25);
        deepstate.observeUnrelatedToken(IERC20(address(unrelatedToken)));

        IDeepstateV1.FillParams[] memory fills = _fills(sellAsset, buyAsset);
        fills[0].fillOrKill = true;
        settler.sell(receiver, sellAsset, buyAsset, 600_000, fills);

        assertTrue(deepstate.allNoRest());
        assertTrue(deepstate.lastFillOrKill());
        assertEq(deepstate.observedInputAllowance(), 60);
        assertEq(deepstate.observedUnrelatedAllowance(), 0);
        assertEq(sellToken.balanceOf(address(settler)), 40);
        assertEq(sellToken.balanceOf(receiver), 10);
        assertEq(sellToken.balanceOf(address(deepstate)), 50);
        assertEq(buyToken.balanceOf(address(settler)), 25);
        assertEq(sellToken.allowance(address(settler), address(deepstate)), 0);
        assertEq(unrelatedToken.allowance(address(settler), address(deepstate)), 0);
    }

    function testFuzz_Deepstate_BoundsERC20Spend(uint128 balance, uint32 rawPpm) public {
        uint256 ppm = bound(rawPpm, 0, BASIS);
        uint256 expectedSellAmount = uint256(balance) * ppm / BASIS;
        sellToken.mint(address(settler), balance);
        deepstate.configure(IERC20(address(sellToken)), IERC20(address(buyToken)), expectedSellAmount, 0);

        settler.sell(receiver, sellAsset, buyAsset, ppm, _fills(sellAsset, buyAsset));

        assertEq(deepstate.observedInputAllowance(), expectedSellAmount);
        assertEq(sellToken.balanceOf(address(deepstate)), expectedSellAmount);
        assertEq(sellToken.balanceOf(address(settler)), uint256(balance) - expectedSellAmount);
        assertEq(sellToken.allowance(address(settler), address(deepstate)), 0);
    }

    function test_Deepstate_ExactAllowancePreventsOverpull() public {
        sellToken.mint(address(settler), 100);
        deepstate.configure(IERC20(address(sellToken)), IERC20(address(buyToken)), 61, 0);

        vm.expectRevert();
        settler.sell(receiver, sellAsset, buyAsset, 600_000, _fills(sellAsset, buyAsset));

        assertEq(sellToken.balanceOf(address(settler)), 100);
        assertEq(sellToken.balanceOf(address(deepstate)), 0);
        assertEq(sellToken.allowance(address(settler), address(deepstate)), 0);
        assertEq(deepstate.callCount(), 0);
    }

    function test_Deepstate_RejectsInexactInputSettlement() public {
        DeepstateFeeOnTransferToken feeToken = new DeepstateFeeOnTransferToken();
        feeToken.mint(address(settler), 100);
        deepstate.configure(IERC20(address(feeToken)), IERC20(address(buyToken)), 100, 0);

        vm.expectRevert(abi.encodeWithSelector(NonStandardDeepstateToken.selector, address(feeToken)));
        IERC20 feeAsset = IERC20(address(feeToken));
        settler.sell(receiver, feeAsset, buyAsset, BASIS, _fills(feeAsset, buyAsset));

        assertEq(feeToken.balanceOf(address(settler)), 100);
        assertEq(feeToken.balanceOf(address(deepstate)), 0);
        assertEq(feeToken.balanceOf(receiver), 0);
    }

    function test_Deepstate_HandlesMaximumERC20BalanceWithoutOverflow() public {
        sellToken.mint(address(settler), type(uint256).max);
        deepstate.configure(IERC20(address(sellToken)), IERC20(address(buyToken)), type(uint256).max, 0);

        settler.sell(receiver, sellAsset, buyAsset, BASIS, _fills(sellAsset, buyAsset));

        assertEq(deepstate.observedInputAllowance(), type(uint256).max);
        assertEq(sellToken.balanceOf(address(settler)), 0);
        assertEq(sellToken.balanceOf(address(deepstate)), type(uint256).max);
        assertEq(sellToken.allowance(address(settler), address(deepstate)), 0);
    }

    function test_Deepstate_RefundsUnspentSelectedNativeInput() public {
        vm.deal(address(settler), 10 ether);
        deepstate.configure(IERC20(address(0)), IERC20(address(buyToken)), 4 ether, 0);

        settler.sell(receiver, ETH_ADDRESS, buyAsset, 600_000, _fills(ETH_ADDRESS, buyAsset));

        assertTrue(deepstate.allNoRest());
        assertEq(deepstate.receivedValue(), 6 ether);
        assertEq(address(settler).balance, 4 ether);
        assertEq(receiver.balance, 2 ether);
        assertEq(address(deepstate).balance, 4 ether);
    }

    function test_Deepstate_ERC20RouteDoesNotForwardUnrelatedNativeBalance() public {
        vm.deal(address(settler), 10 ether);
        sellToken.mint(address(settler), 100);
        deepstate.configure(IERC20(address(sellToken)), IERC20(address(buyToken)), 100, 0);

        settler.sell(receiver, sellAsset, buyAsset, BASIS, _fills(sellAsset, buyAsset));

        assertEq(deepstate.receivedValue(), 0);
        assertEq(address(settler).balance, 10 ether);
        assertEq(address(deepstate).balance, 0);
    }

    function test_Deepstate_RevertIsAtomic() public {
        sellToken.mint(address(settler), 100);
        deepstate.configure(IERC20(address(sellToken)), IERC20(address(buyToken)), 60, 0);
        deepstate.setShouldRevert(true);

        vm.expectRevert(DeepstatePoolMock.FillFailed.selector);
        settler.sell(receiver, sellAsset, buyAsset, 600_000, _fills(sellAsset, buyAsset));

        assertEq(sellToken.balanceOf(address(settler)), 100);
        assertEq(sellToken.balanceOf(address(deepstate)), 0);
        assertEq(sellToken.allowance(address(settler), address(deepstate)), 0);
    }

    function test_Deepstate_RejectsInvalidRoutes() public {
        IDeepstateV1.FillParams[] memory fills = new IDeepstateV1.FillParams[](0);
        vm.expectRevert(InvalidDeepstateRoute.selector);
        settler.sell(receiver, sellAsset, buyAsset, BASIS, fills);

        vm.expectRevert(InvalidDeepstateRoute.selector);
        settler.sell(receiver, sellAsset, sellAsset, BASIS, _fills(sellAsset, buyAsset));

        fills = _fills(sellAsset, buyAsset);
        fills[0].isBid = !fills[0].isBid;
        vm.expectRevert(InvalidDeepstateRoute.selector);
        settler.sell(receiver, sellAsset, buyAsset, BASIS, fills);

        fills = _fills(sellAsset, buyAsset);
        fills[0].token1 = address(0xCAFE);
        vm.expectRevert(InvalidDeepstateRoute.selector);
        settler.sell(receiver, sellAsset, buyAsset, BASIS, fills);
    }

    function test_Deepstate_ActionEncodingUsesPinnedEngineABI() public pure {
        IDeepstateV1.FillParams[] memory fills = new IDeepstateV1.FillParams[](0);
        bytes memory action = abi.encodeCall(ISettlerActions.DEEPSTATE, (address(ETH_ADDRESS), BASIS, fills));

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
        RobinHoodSettler deployedSettler =
            RobinHoodSettler(payable(deployCode("TakerSubmitted.sol:RobinHoodSettler", abi.encode(bytes20(0)))));
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(
            ISettlerActions.BASIC, (address(sellToken), BASIS, address(ROBINHOOD_DEEPSTATE), 0, bytes(""))
        );

        vm.expectRevert(ConfusedDeputy.selector);
        deployedSettler.execute(
            ISettlerBase.AllowedSlippage({recipient: receiver, buyToken: IERC20(address(0)), minAmountOut: 0}),
            actions,
            bytes32(0)
        );

        assertEq(deepstate.callCount(), 0);
        assertEq(sellToken.allowance(address(deployedSettler), address(deepstate)), 0);
    }

    function test_Deepstate_ActionDispatchesThroughRobinHoodSettler() public {
        RobinHoodSettler deployedSettler =
            RobinHoodSettler(payable(deployCode("TakerSubmitted.sol:RobinHoodSettler", abi.encode(bytes20(0)))));
        sellToken.mint(address(deployedSettler), 100);
        buyToken.mint(address(deepstate), 25);
        deepstate.configure(IERC20(address(sellToken)), IERC20(address(buyToken)), 60, 25);

        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(ISettlerActions.DEEPSTATE, (address(sellToken), BASIS, _fills(sellAsset, buyAsset)));

        deployedSettler.execute(
            ISettlerBase.AllowedSlippage({recipient: receiver, buyToken: buyAsset, minAmountOut: 25}),
            actions,
            bytes32(0)
        );

        assertTrue(deepstate.allNoRest());
        assertEq(sellToken.balanceOf(receiver), 40);
        assertEq(sellToken.balanceOf(address(deepstate)), 60);
        assertEq(buyToken.balanceOf(receiver), 25);
        assertEq(sellToken.allowance(address(deployedSettler), address(deepstate)), 0);
    }

    function test_Deepstate_ActionEnforcesTransactionSlippage() public {
        RobinHoodSettler deployedSettler =
            RobinHoodSettler(payable(deployCode("TakerSubmitted.sol:RobinHoodSettler", abi.encode(bytes20(0)))));
        sellToken.mint(address(deployedSettler), 100);
        buyToken.mint(address(deepstate), 24);
        deepstate.configure(sellAsset, buyAsset, 60, 24);

        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(ISettlerActions.DEEPSTATE, (address(sellToken), BASIS, _fills(sellAsset, buyAsset)));

        vm.expectRevert(abi.encodeWithSelector(TooMuchSlippage.selector, address(buyToken), 25, 24));
        deployedSettler.execute(
            ISettlerBase.AllowedSlippage({recipient: receiver, buyToken: buyAsset, minAmountOut: 25}),
            actions,
            bytes32(0)
        );

        assertEq(sellToken.balanceOf(address(deployedSettler)), 100);
        assertEq(sellToken.balanceOf(address(deepstate)), 0);
        assertEq(buyToken.balanceOf(receiver), 0);
        assertEq(sellToken.allowance(address(deployedSettler), address(deepstate)), 0);
    }

    function test_Deepstate_ActionPaysOutNativeOutput() public {
        RobinHoodSettler deployedSettler =
            RobinHoodSettler(payable(deployCode("TakerSubmitted.sol:RobinHoodSettler", abi.encode(bytes20(0)))));
        sellToken.mint(address(deployedSettler), 100);
        vm.deal(address(deepstate), 25);
        deepstate.configure(sellAsset, IERC20(address(0)), 60, 25);

        bytes[] memory actions = new bytes[](1);
        actions[0] =
            abi.encodeCall(ISettlerActions.DEEPSTATE, (address(sellToken), BASIS, _fills(sellAsset, ETH_ADDRESS)));

        deployedSettler.execute(
            ISettlerBase.AllowedSlippage({recipient: receiver, buyToken: ETH_ADDRESS, minAmountOut: 25}),
            actions,
            bytes32(0)
        );

        assertEq(receiver.balance, 25);
        assertEq(sellToken.balanceOf(receiver), 40);
        assertEq(address(deployedSettler).balance, 0);
        assertEq(sellToken.allowance(address(deployedSettler), address(deepstate)), 0);
    }

    function test_Deepstate_ActionIsUnavailableOutsideRobinHood() public {
        BaseSettler baseSettler =
            BaseSettler(payable(deployCode("TakerSubmitted.sol:BaseSettler", abi.encode(bytes20(0)))));
        bytes memory actionData = abi.encode(address(sellToken), BASIS, _fills(sellAsset, buyAsset));
        bytes[] memory actions = new bytes[](1);
        actions[0] = bytes.concat(ISettlerActions.DEEPSTATE.selector, actionData);

        vm.expectRevert(
            abi.encodeWithSelector(ActionInvalid.selector, 0, ISettlerActions.DEEPSTATE.selector, actionData)
        );
        baseSettler.execute(
            ISettlerBase.AllowedSlippage({recipient: receiver, buyToken: buyAsset, minAmountOut: 0}),
            actions,
            bytes32(0)
        );
    }

    function _fills(IERC20 inputToken, IERC20 outputToken)
        private
        pure
        returns (IDeepstateV1.FillParams[] memory fills)
    {
        address inputAsset = address(inputToken) == address(ETH_ADDRESS) ? address(0) : address(inputToken);
        address outputAsset = address(outputToken) == address(ETH_ADDRESS) ? address(0) : address(outputToken);
        bool isBid = inputAsset > outputAsset;

        fills = new IDeepstateV1.FillParams[](1);
        fills[0] = IDeepstateV1.FillParams({
            token0: isBid ? outputAsset : inputAsset,
            token1: isBid ? inputAsset : outputAsset,
            epoch: 0,
            order: bytes32(0),
            isBid: isBid,
            noRest: false,
            fillOrKill: false
        });
    }
}
