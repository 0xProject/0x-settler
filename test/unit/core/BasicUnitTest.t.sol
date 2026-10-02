// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Basic} from "src/core/Basic.sol";
import {Permit2PaymentTakerSubmitted} from "src/core/Permit2Payment.sol";
import {Permit2PaymentAbstract} from "src/core/Permit2PaymentAbstract.sol";
import {AllowanceHolderContext} from "src/allowanceholder/AllowanceHolderContext.sol";
import {BaseSettler} from "src/chains/Base/TakerSubmitted.sol";
import {BaseSettlerMetaTxn} from "src/chains/Base/MetaTxn.sol";
import {TempoSettler} from "src/chains/Tempo/TakerSubmitted.sol";
import {TempoSettlerMetaTxn} from "src/chains/Tempo/MetaTxn.sol";
import {TempoSettlerIntent} from "src/chains/Tempo/Intent.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {IUniV2Pair} from "src/core/UniswapV2.sol";
import {IVelodromePair} from "src/core/Velodrome.sol";
import {IDodoV2} from "src/core/DodoV2.sol";
import {IMaverickV2Pool} from "src/core/MaverickV2.sol";
import {ReceivePolicyBlocked} from "src/core/SettlerErrors.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";

import {uint512} from "src/utils/512Math.sol";

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {Utils, RejectionFallbackDummy} from "../Utils.sol";

import {Test} from "@forge-std/Test.sol";
import {MockERC20} from "@solmate/test/utils/mocks/MockERC20.sol";

contract BasicDummy is Permit2PaymentTakerSubmitted, Basic {
    function sellToPool(IERC20 sellToken, uint256 ppm, address pool, uint256 offset, bytes memory data) public {
        super.basicSellToPool(sellToken, ppm, pool, offset, data);
    }

    function _tokenId() internal pure override returns (uint256) {
        revert("unimplemented");
    }

    function _hasMetaTxn() internal pure override returns (bool) {
        return false;
    }

    function _div512to256(uint512, uint512) internal view override returns (uint256) {
        revert("unimplemented");
    }

    function _isRestrictedTarget(address target)
        internal
        view
        override(Permit2PaymentTakerSubmitted, Permit2PaymentAbstract)
        returns (bool)
    {
        return super._isRestrictedTarget(target);
    }
}

contract BasicUnitTest is Utils, Test {
    BasicDummy basic;
    address PERMIT2 = _etchNamedRejectionDummy("PERMIT2", 0x000000000022D473030F116dDEE9F6B43aC78BA3);
    address ALLOWANCE_HOLDER = _etchNamedRejectionDummy("ALLOWANCE_HOLDER", 0x0000000000001fF3684f28c67538d4D072C22734);
    address POOL = _createNamedRejectionDummy("POOL");
    IERC20 TOKEN = IERC20(_createNamedRejectionDummy("TOKEN"));

    function setUp() public {
        basic = new BasicDummy();
    }

    function testBasicSell() public {
        uint256 ppm = 1_000_000;
        uint256 offset = 4;
        uint256 amount = 99999;
        bytes4 selector = bytes4(hex"12345678");
        bytes memory data = abi.encodePacked(selector, amount);

        _mockExpectCall(
            address(TOKEN), abi.encodeWithSelector(IERC20.balanceOf.selector, address(basic)), abi.encode(amount)
        );
        _mockExpectCall(
            address(TOKEN),
            abi.encodeWithSelector(IERC20.allowance.selector, address(basic), address(POOL)),
            abi.encode(amount)
        );

        _mockExpectCall(address(POOL), data, abi.encode(true));

        basic.sellToPool(TOKEN, ppm, POOL, offset, data);
    }

    /// @dev adjust the balange of the contract to be less than expected
    function testBasicSellLowerBalanceAmount() public {
        uint256 ppm = 1_000_000;
        uint256 offset = 4;
        uint256 amount = 99999;
        bytes4 selector = bytes4(hex"12345678");
        bytes memory data = abi.encodePacked(selector, amount);

        _mockExpectCall(
            address(TOKEN), abi.encodeWithSelector(IERC20.balanceOf.selector, address(basic)), abi.encode(amount / 2)
        );
        _mockExpectCall(
            address(TOKEN),
            abi.encodeWithSelector(IERC20.allowance.selector, address(basic), address(POOL)),
            abi.encode(amount)
        );

        _mockExpectCall(address(POOL), abi.encodePacked(selector, amount / 2), abi.encode(true));
        basic.sellToPool(TOKEN, ppm, POOL, offset, data);
    }

    /// @dev adjust the balange of the contract to be greater than expected
    function testBasicSellGreaterBalanceAmount() public {
        uint256 ppm = 1_000_000;
        uint256 offset = 4;
        uint256 amount = 99999;
        bytes4 selector = bytes4(hex"12345678");
        bytes memory data = abi.encodePacked(selector, amount);

        _mockExpectCall(
            address(TOKEN), abi.encodeWithSelector(IERC20.balanceOf.selector, address(basic)), abi.encode(amount * 2)
        );
        _mockExpectCall(
            address(TOKEN),
            abi.encodeWithSelector(IERC20.allowance.selector, address(basic), address(POOL)),
            abi.encode(amount * 2)
        );

        _mockExpectCall(address(POOL), abi.encodePacked(selector, amount * 2), abi.encode(true));
        basic.sellToPool(TOKEN, ppm, POOL, offset, data);
    }

    /// @dev When 0xeeee (native asset) is used we expect it to transfer as value
    function testBasicSellEthValue() public {
        uint256 ppm = 1_000_000;
        uint256 offset = 4;
        uint256 amount = 99999;
        uint256 value = amount;
        bytes4 selector = bytes4(hex"12345678");
        bytes memory data = abi.encodePacked(selector, amount);

        _mockExpectCall(address(POOL), value, abi.encodePacked(selector, amount), abi.encode(true));

        vm.deal(address(basic), value);
        basic.sellToPool(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), ppm, POOL, offset, data);
    }

    /// @dev When 0xeeee (native asset) is used we expect it to transfer as value and adjust for the current balance if lower
    function testBasicSellLowerEthValue() public {
        uint256 ppm = 1_000_000;
        uint256 offset = 4;
        uint256 amount = 99999;
        uint256 value = amount / 2;
        bytes4 selector = bytes4(hex"12345678");
        bytes memory data = abi.encodePacked(selector, amount);

        _mockExpectCall(address(POOL), value, abi.encodePacked(selector, value), abi.encode(true));

        vm.deal(address(basic), value);
        basic.sellToPool(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), ppm, POOL, offset, data);
    }

    /// @dev When 0xeeee (native asset) is used we expect it to transfer as value and adjust for the current balance if greater
    function testBasicSellGreaterEthValue() public {
        uint256 ppm = 1_000_000;
        uint256 offset = 4;
        uint256 amount = 99999;
        uint256 value = amount * 2;
        bytes4 selector = bytes4(hex"12345678");
        bytes memory data = abi.encodePacked(selector, amount);

        _mockExpectCall(address(POOL), value, abi.encodePacked(selector, value), abi.encode(true));

        vm.deal(address(basic), value);
        basic.sellToPool(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), ppm, POOL, offset, data);
    }

    /// @dev When 0xeeee (native asset) is used we expect it to transfer as value and adjust for the current balance
    function testBasicSellAdjustedEthValue() public {
        uint256 ppm = 500_000; // sell half
        uint256 offset = 4;
        uint256 amount = 99999;
        uint256 value = amount * 2;
        bytes4 selector = bytes4(hex"12345678");
        bytes memory data = abi.encodePacked(selector, amount);

        // 500_000 / 1_000_000 * value == amount
        _mockExpectCall(address(POOL), amount, abi.encodePacked(selector, amount), abi.encode(true));

        vm.deal(address(basic), value);
        basic.sellToPool(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), ppm, POOL, offset, data);
    }

    /// @dev A proportion below one basis point (here 30 ppm) sells a nonzero amount
    function testBasicSellSubBasisPointProportion() public {
        uint256 ppm = 30;
        uint256 offset = 4;
        uint256 value = 1_000_000;
        uint256 amount = 30;
        bytes4 selector = bytes4(hex"12345678");
        bytes memory data = abi.encodePacked(selector, amount);

        // 30 / 1_000_000 * value == amount
        _mockExpectCall(address(POOL), amount, abi.encodePacked(selector, amount), abi.encode(true));

        vm.deal(address(basic), value);
        basic.sellToPool(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), ppm, POOL, offset, data);
    }

    /// @dev When 0xeeee (native asset) is used we expect it to support a transfer with no data
    function testBasicSellTransferValue() public {
        uint256 ppm = 1_000_000;
        uint256 offset = 0;
        uint256 amount = 99999;
        uint256 value = amount;
        bytes memory data;

        _mockExpectCall(address(POOL), value, data, abi.encode(true));

        vm.deal(address(basic), value);
        basic.sellToPool(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), ppm, POOL, offset, data);
    }

    function testBasicRestrictedTarget() public {
        uint256 ppm = 1_000_000;
        uint256 offset = 0;
        bytes memory data;

        vm.expectRevert();
        basic.sellToPool(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), ppm, PERMIT2, offset, data);

        vm.expectRevert();
        basic.sellToPool(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), ppm, ALLOWANCE_HOLDER, offset, data);
    }

    function testBasicBubblesUpRevert() public {
        uint256 ppm = 1_000_000;
        uint256 offset = 0;
        bytes memory data;

        vm.expectRevert();
        basic.sellToPool(IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE), ppm, POOL, offset, data);
    }
}

contract PositiveSlippageUnitTest is Test {
    uint256 private constant BASIS = 1_000_000;
    IERC20 private constant ETH_ADDRESS = IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE);

    BaseSettler private settler;
    MockERC20 private token;
    address payable private recipient;

    function setUp() public {
        settler = new BaseSettler(bytes20(0));
        token = new MockERC20("Test Token", "TT", 18);
        recipient = payable(makeAddr("recipient"));
    }

    function test_PositiveSlippage_TransfersProportionOfTokenSurplus() public {
        _executeToken(2_000_000, 1_000_000, 250_000, BASIS);

        assertEq(token.balanceOf(recipient), 250_000);
        assertEq(token.balanceOf(address(settler)), 1_750_000);
    }

    function test_PositiveSlippage_CapsTokenTransfer() public {
        _executeToken(2_000_000, 1_000_000, 750_000, 100_000);

        assertEq(token.balanceOf(recipient), 200_000);
        assertEq(token.balanceOf(address(settler)), 1_800_000);
    }

    function test_PositiveSlippage_DoesNotTransferWithoutSurplus() public {
        _executeToken(1_000_000, 1_500_000, BASIS, BASIS);

        assertEq(token.balanceOf(recipient), 0);
        assertEq(token.balanceOf(address(settler)), 1_000_000);
    }

    function test_PositiveSlippage_TransfersProportionOfEthSurplus() public {
        vm.deal(address(settler), 2_000_000);
        _execute(ETH_ADDRESS, 1_000_000, 250_000, BASIS);

        assertEq(recipient.balance, 250_000);
        assertEq(address(settler).balance, 1_750_000);
    }

    function testFuzz_PositiveSlippage_TransfersExpectedTokenAmount(
        uint128 balance,
        uint128 expectedAmount,
        uint24 surplusPpm,
        uint24 maxPpm
    ) public {
        expectedAmount = uint128(bound(expectedAmount, 0, balance));
        surplusPpm = uint24(bound(surplusPpm, 0, BASIS));
        maxPpm = uint24(bound(maxPpm, 0, BASIS));

        _executeToken(balance, expectedAmount, surplusPpm, maxPpm);

        uint256 proportionalAmount = (uint256(balance) - expectedAmount) * surplusPpm / BASIS;
        uint256 cappedAmount = uint256(balance) * maxPpm / BASIS;
        uint256 transferredAmount = proportionalAmount < cappedAmount ? proportionalAmount : cappedAmount;
        assertEq(token.balanceOf(recipient), transferredAmount);
        assertEq(token.balanceOf(address(settler)), uint256(balance) - transferredAmount);
    }

    function _executeToken(uint256 balance, uint256 expectedAmount, uint256 surplusPpm, uint256 maxPpm) private {
        token.mint(address(settler), balance);
        _execute(IERC20(address(token)), expectedAmount, surplusPpm, maxPpm);
    }

    function _execute(IERC20 asset, uint256 expectedAmount, uint256 surplusPpm, uint256 maxPpm) private {
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(
            ISettlerActions.POSITIVE_SLIPPAGE, (recipient, address(asset), expectedAmount, surplusPpm, maxPpm)
        );
        settler.execute(
            ISettlerBase.AllowedSlippage({
                recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
            }),
            actions,
            bytes32(0)
        );
    }
}

contract RecipientCheckSettler is BaseSettler {
    address private immutable expectedRecipient;
    IERC20 private immutable expectedBuyToken;

    constructor(address recipient, IERC20 buyToken) BaseSettler(bytes20(0)) {
        expectedRecipient = recipient;
        expectedBuyToken = buyToken;
    }

    function _hasRecipientCheck() internal pure override returns (bool) {
        return true;
    }

    function _checkRecipient(address recipient, IERC20 buyToken) internal view override {
        require(recipient == expectedRecipient && buyToken == expectedBuyToken);
        revert ReceivePolicyBlocked(recipient);
    }
}

contract RecipientCheckMetaTxn is BaseSettlerMetaTxn {
    address private immutable expectedRecipient;
    IERC20 private immutable expectedBuyToken;

    constructor(address recipient, IERC20 buyToken) BaseSettlerMetaTxn(bytes20(0)) {
        expectedRecipient = recipient;
        expectedBuyToken = buyToken;
    }

    function _hasRecipientCheck() internal pure override returns (bool) {
        return true;
    }

    function _checkRecipient(address recipient, IERC20 buyToken) internal view override {
        require(recipient == expectedRecipient && buyToken == expectedBuyToken);
        revert ReceivePolicyBlocked(recipient);
    }
}

contract RecipientCheckUnitTest is Test {
    RecipientCheckSettler private settler;
    MockERC20 private sellToken;
    MockERC20 private buyToken;
    address payable private recipient;
    address private pool;

    function setUp() public {
        sellToken = new MockERC20("Sell Token", "SELL", 18);
        buyToken = new MockERC20("Buy Token", "BUY", 18);
        recipient = payable(makeAddr("recipient"));
        pool = address(new RejectionFallbackDummy());
        settler = RecipientCheckSettler(
            payable(deployCode("BasicUnitTest.t.sol:RecipientCheckSettler", abi.encode(recipient, buyToken)))
        );
        sellToken.mint(address(settler), 1 ether);
        buyToken.mint(address(settler), 1 ether);
    }

    function test_RecipientCheck_FinalTransfer_Reverts() public {
        vm.expectRevert(abi.encodeWithSelector(ReceivePolicyBlocked.selector, recipient));
        settler.execute(
            ISettlerBase.AllowedSlippage(recipient, IERC20(address(buyToken)), 1), new bytes[](0), bytes32(0)
        );
        assertEq(buyToken.balanceOf(address(settler)), 1 ether);
        assertEq(buyToken.balanceOf(recipient), 0);
    }

    function test_RecipientCheck_NativeTransfer_Reverts() public {
        IERC20 eth = IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE);
        RecipientCheckSettler nativeSettler = RecipientCheckSettler(
            payable(deployCode("BasicUnitTest.t.sol:RecipientCheckSettler", abi.encode(recipient, eth)))
        );
        vm.deal(address(nativeSettler), 1 ether);
        vm.expectRevert(abi.encodeWithSelector(ReceivePolicyBlocked.selector, recipient));
        nativeSettler.execute(ISettlerBase.AllowedSlippage(recipient, eth, 1), new bytes[](0), bytes32(0));
        assertEq(address(nativeSettler).balance, 1 ether);
    }

    function test_RecipientCheck_CheckSlippage_Reverts() public {
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(ISettlerActions.CHECK_SLIPPAGE, (true));
        vm.expectRevert(abi.encodeWithSelector(ReceivePolicyBlocked.selector, recipient));
        settler.execute(ISettlerBase.AllowedSlippage(recipient, IERC20(address(buyToken)), 1), actions, bytes32(0));
    }

    function test_RecipientCheck_PositiveSlippage_Reverts() public {
        _expectBlocked(
            abi.encodeCall(ISettlerActions.POSITIVE_SLIPPAGE, (recipient, address(buyToken), 0, 1_000_000, 1_000_000))
        );
    }

    function test_RecipientCheck_PositiveSlippage_WithoutSurplus_Reverts() public {
        _expectBlocked(
            abi.encodeCall(
                ISettlerActions.POSITIVE_SLIPPAGE, (recipient, address(buyToken), 1 ether, 1_000_000, 1_000_000)
            )
        );
    }

    function test_RecipientCheck_TransferFrom_Reverts() public {
        _expectBlocked(abi.encodeCall(ISettlerActions.TRANSFER_FROM, (recipient, _permit(address(buyToken)), "")));
    }

    function test_RecipientCheck_MetaTxnTransferFrom_Reverts() public {
        RecipientCheckMetaTxn metaTxn = RecipientCheckMetaTxn(
            payable(deployCode("BasicUnitTest.t.sol:RecipientCheckMetaTxn", abi.encode(recipient, buyToken)))
        );
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(ISettlerActions.METATXN_TRANSFER_FROM, (recipient, _permit(address(buyToken))));
        vm.expectRevert(abi.encodeWithSelector(ReceivePolicyBlocked.selector, recipient));
        metaTxn.executeMetaTxn(_noSlippage(), actions, bytes32(0), recipient, "");
    }

    function test_RecipientCheck_Rfq_Reverts() public {
        _expectBlocked(
            abi.encodeCall(
                ISettlerActions.RFQ,
                (recipient, _permit(address(buyToken)), address(this), "", address(sellToken), 1 ether)
            )
        );
    }

    function test_RecipientCheck_UniswapV2_BothDirections_Revert() public {
        vm.mockCall(
            pool,
            abi.encodeCall(IUniV2Pair.getReserves, ()),
            abi.encode(uint112(100 ether), uint112(100 ether), uint32(0))
        );
        for (uint24 direction; direction < 2; ++direction) {
            vm.mockCall(pool, abi.encodeCall(IUniV2Pair.token0, ()), abi.encode(direction == 1 ? sellToken : buyToken));
            vm.mockCall(pool, abi.encodeCall(IUniV2Pair.token1, ()), abi.encode(direction == 1 ? buyToken : sellToken));
            _expectBlocked(
                abi.encodeCall(
                    ISettlerActions.UNISWAPV2, (recipient, address(sellToken), 1_000_000, pool, direction, 0)
                )
            );
        }
    }

    function test_RecipientCheck_UniswapV3_Reverts() public {
        bytes memory path = abi.encodePacked(address(sellToken), uint8(0), uint24(500), uint160(0), address(buyToken));
        _expectBlocked(abi.encodeCall(ISettlerActions.UNISWAPV3, (recipient, 1_000_000, path, 0)));
    }

    function test_RecipientCheck_UniswapV3VIP_Reverts() public {
        bytes memory path = abi.encodePacked(uint8(0), uint24(500), uint160(0), address(buyToken));
        _expectBlocked(
            abi.encodeCall(ISettlerActions.UNISWAPV3_VIP, (recipient, _permit(address(sellToken)), path, "", 0))
        );
    }

    function test_RecipientCheck_Velodrome_BothDirections_Revert() public {
        for (uint24 direction; direction < 2; ++direction) {
            vm.mockCall(
                pool,
                abi.encodeCall(IVelodromePair.metadata, ()),
                abi.encode(
                    1 ether,
                    1 ether,
                    100 ether,
                    100 ether,
                    true,
                    direction == 1 ? sellToken : buyToken,
                    direction == 1 ? buyToken : sellToken
                )
            );
            _expectBlocked(abi.encodeCall(ISettlerActions.VELODROME, (recipient, 1_000_000, pool, direction, 0)));
        }
    }

    function test_RecipientCheck_DodoV2_BothDirections_Revert() public {
        for (uint256 direction; direction < 2; ++direction) {
            vm.mockCall(
                pool, abi.encodeCall(IDodoV2._BASE_TOKEN_, ()), abi.encode(direction == 1 ? buyToken : sellToken)
            );
            vm.mockCall(
                pool, abi.encodeCall(IDodoV2._QUOTE_TOKEN_, ()), abi.encode(direction == 1 ? sellToken : buyToken)
            );
            _expectBlocked(
                abi.encodeCall(
                    ISettlerActions.DODOV2, (recipient, address(sellToken), 1_000_000, pool, direction == 1, 0)
                )
            );
        }
    }

    function test_RecipientCheck_MaverickV2_BothDirections_Revert() public {
        for (uint256 direction; direction < 2; ++direction) {
            vm.mockCall(
                pool, abi.encodeCall(IMaverickV2Pool.tokenA, ()), abi.encode(direction == 1 ? sellToken : buyToken)
            );
            vm.mockCall(
                pool, abi.encodeCall(IMaverickV2Pool.tokenB, ()), abi.encode(direction == 1 ? buyToken : sellToken)
            );
            _expectBlocked(
                abi.encodeCall(
                    ISettlerActions.MAVERICKV2, (recipient, address(sellToken), 1_000_000, pool, direction == 1, 0, 0)
                )
            );
        }
    }

    function test_RecipientCheck_Default_DodoV2_DoesNotReadBuyToken() public {
        vm.mockCall(pool, abi.encodeWithSelector(IDodoV2.sellBase.selector), abi.encode(1 ether));
        vm.mockCall(pool, abi.encodeWithSelector(IDodoV2.sellQuote.selector), abi.encode(1 ether));
        for (uint256 direction; direction < 2; ++direction) {
            _executeDefault(
                abi.encodeCall(
                    ISettlerActions.DODOV2, (recipient, address(sellToken), 1_000_000, pool, direction == 1, 0)
                )
            );
        }
    }

    function test_RecipientCheck_Default_MaverickV2_DoesNotReadBuyToken() public {
        vm.mockCall(pool, abi.encodeWithSelector(IMaverickV2Pool.swap.selector), abi.encode(1 ether, 1 ether));
        for (uint256 direction; direction < 2; ++direction) {
            _executeDefault(
                abi.encodeCall(
                    ISettlerActions.MAVERICKV2, (recipient, address(sellToken), 1_000_000, pool, direction == 1, 0, 0)
                )
            );
        }
    }

    function test_RecipientCheck_Bebop_Reverts() public {
        ISettlerActions.BebopOrder memory order;
        order.maker_token = address(buyToken);
        ISettlerActions.BebopMakerSignature memory signature;
        _expectBlocked(abi.encodeCall(ISettlerActions.BEBOP, (recipient, address(sellToken), order, signature, 0)));
    }

    function test_RecipientCheck_Renegade_Reverts() public {
        _expectBlocked(
            abi.encodeCall(
                ISettlerActions.RENEGADE,
                (recipient, address(sellToken), address(buyToken), 1 ether, false, 0, new bytes(0x120), 0)
            )
        );
    }

    function test_RecipientCheck_Basic_TransfersWithoutCheck() public {
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(
            ISettlerActions.BASIC,
            (address(0), 0, address(buyToken), 0, abi.encodeCall(IERC20.transfer, (recipient, 1 ether)))
        );
        settler.execute(_noSlippage(), actions, bytes32(0));
        assertEq(buyToken.balanceOf(recipient), 1 ether);
    }

    function _expectBlocked(bytes memory action) private {
        bytes[] memory actions = new bytes[](1);
        actions[0] = action;
        vm.expectRevert(abi.encodeWithSelector(ReceivePolicyBlocked.selector, recipient));
        settler.execute(_noSlippage(), actions, bytes32(0));
        assertEq(sellToken.balanceOf(address(settler)), 1 ether);
        assertEq(buyToken.balanceOf(address(settler)), 1 ether);
    }

    function _executeDefault(bytes memory action) private {
        BaseSettler defaultSettler =
            BaseSettler(payable(deployCode("TakerSubmitted.sol:BaseSettler", abi.encode(bytes20(0)))));
        sellToken.mint(address(defaultSettler), 1 ether);
        bytes[] memory actions = new bytes[](1);
        actions[0] = action;
        assertTrue(defaultSettler.execute(_noSlippage(), actions, bytes32(0)));
        assertEq(sellToken.balanceOf(address(defaultSettler)), 0);
    }

    function _noSlippage() private pure returns (ISettlerBase.AllowedSlippage memory) {
        return ISettlerBase.AllowedSlippage(payable(address(0)), IERC20(address(0)), 0);
    }

    function _permit(address token) private view returns (ISignatureTransfer.PermitTransferFrom memory) {
        return
            ISignatureTransfer.PermitTransferFrom(
                ISignatureTransfer.TokenPermissions(token, 1 ether), 0, block.timestamp
            );
    }
}

contract TempoRecipientCheckHarness is TempoSettler {
    constructor() TempoSettler(bytes20(0)) {}

    function hasRecipientCheck() external pure returns (bool) {
        return _hasRecipientCheck();
    }
}

contract TempoMetaTxnRecipientCheckHarness is TempoSettlerMetaTxn {
    constructor() TempoSettlerMetaTxn(bytes20(0)) {}

    function hasRecipientCheck() external pure returns (bool) {
        return _hasRecipientCheck();
    }
}

contract TempoIntentRecipientCheckHarness is TempoSettlerIntent {
    constructor() TempoSettlerIntent(bytes20(0)) {}

    function hasRecipientCheck() external pure returns (bool) {
        return _hasRecipientCheck();
    }
}

contract TempoRecipientCheckUnitTest is Test {
    function test_RecipientCheck_TempoTaker_Enabled() public {
        TempoRecipientCheckHarness settler =
            TempoRecipientCheckHarness(payable(deployCode("BasicUnitTest.t.sol:TempoRecipientCheckHarness")));
        assertTrue(settler.hasRecipientCheck());
    }

    function test_RecipientCheck_TempoMetaTxn_Enabled() public {
        TempoMetaTxnRecipientCheckHarness settler = TempoMetaTxnRecipientCheckHarness(
            payable(deployCode("BasicUnitTest.t.sol:TempoMetaTxnRecipientCheckHarness"))
        );
        assertTrue(settler.hasRecipientCheck());
    }

    function test_RecipientCheck_TempoIntent_Enabled() public {
        TempoIntentRecipientCheckHarness settler = TempoIntentRecipientCheckHarness(
            payable(deployCode("BasicUnitTest.t.sol:TempoIntentRecipientCheckHarness"))
        );
        assertTrue(settler.hasRecipientCheck());
    }
}
