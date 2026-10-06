// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {MockERC20} from "@solmate/test/utils/mocks/MockERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {SettlerAbstract} from "src/SettlerAbstract.sol";
import {SettlerBase} from "src/SettlerBase.sol";
import {BaseSettler} from "src/chains/Base/TakerSubmitted.sol";
import {BaseSettlerMetaTxn} from "src/chains/Base/MetaTxn.sol";
import {TempoSettler} from "src/chains/Tempo/TakerSubmitted.sol";
import {TempoSettlerMetaTxn} from "src/chains/Tempo/MetaTxn.sol";
import {TempoSettlerIntent} from "src/chains/Tempo/Intent.sol";
import {uniswapV3BaseFactory, uniswapV3InitHash, IUniswapV3Callback} from "src/core/univ3forks/UniswapV3.sol";
import {ALLOWANCE_HOLDER} from "src/allowanceholder/IAllowanceHolder.sol";
import {ConfusedDeputy} from "src/core/SettlerErrors.sol";
import {IRenegadeGasSponsor} from "src/core/Renegade.sol";
import {IUniV2Pair} from "src/core/UniswapV2.sol";
import {IVelodromePair} from "src/core/Velodrome.sol";
import {IDodoV2} from "src/core/DodoV2.sol";
import {IMaverickV2Pool} from "src/core/MaverickV2.sol";
import {ReceivePolicyBlocked} from "src/core/SettlerErrors.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {RejectionFallbackDummy} from "../Utils.sol";

contract RecipientCheckSettler is BaseSettler {
    address public expectedRecipient;
    IERC20 private expectedBuyToken;
    address private expectedSender;

    constructor(address recipient, IERC20 buyToken) BaseSettler(bytes20(0)) {
        expectedRecipient = recipient;
        expectedBuyToken = buyToken;
        expectedSender = address(this);
    }

    function expectTransfer(address sender, address recipient, IERC20 token) external {
        expectedSender = sender;
        expectedRecipient = recipient;
        expectedBuyToken = token;
    }

    function _hasRecipientCheck() internal pure override(SettlerAbstract, SettlerBase) returns (bool) {
        return true;
    }

    function _checkRecipient(address sender, address recipient, IERC20 buyToken)
        internal
        view
        override(SettlerAbstract, SettlerBase)
    {
        if (recipient == expectedRecipient && buyToken == expectedBuyToken) {
            require(sender == expectedSender, "incorrect sender");
            revert ReceivePolicyBlocked(recipient);
        }
    }
}

contract RecipientCheckMetaTxn is BaseSettlerMetaTxn {
    address public expectedRecipient;
    IERC20 private expectedBuyToken;
    address private expectedSender;

    constructor(address recipient, IERC20 buyToken) BaseSettlerMetaTxn(bytes20(0)) {
        expectedRecipient = recipient;
        expectedBuyToken = buyToken;
        expectedSender = address(this);
    }

    function expectTransfer(address sender, address recipient, IERC20 token) external {
        expectedSender = sender;
        expectedRecipient = recipient;
        expectedBuyToken = token;
    }

    function _hasRecipientCheck() internal pure override(SettlerAbstract, SettlerBase) returns (bool) {
        return true;
    }

    function _checkRecipient(address sender, address recipient, IERC20 buyToken)
        internal
        view
        override(SettlerAbstract, SettlerBase)
    {
        if (recipient == expectedRecipient && buyToken == expectedBuyToken) {
            require(sender == expectedSender, "incorrect sender");
            revert ReceivePolicyBlocked(recipient);
        }
    }
}

contract RecipientCheckV3Pool {
    function swap(address, bool zeroForOne, int256 amount, uint160, bytes calldata data)
        external
        returns (int256, int256)
    {
        (int256 amount0, int256 amount1) = zeroForOne ? (amount, -amount) : (-amount, amount);
        IUniswapV3Callback(msg.sender).uniswapV3SwapCallback(amount0, amount1, data);
        return (amount0, amount1);
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
            payable(deployCode("SettlerRecipientCheck.t.sol:RecipientCheckSettler", abi.encode(recipient, buyToken)))
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
            payable(deployCode("SettlerRecipientCheck.t.sol:RecipientCheckSettler", abi.encode(recipient, eth)))
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
        settler.expectTransfer(address(this), recipient, IERC20(address(buyToken)));
        _expectBlocked(abi.encodeCall(ISettlerActions.TRANSFER_FROM, (recipient, _permit(address(buyToken)), "")));
    }

    function test_RecipientCheck_ForwardedTransferFrom_UsesPayer() public {
        address payer = makeAddr("payer");
        settler.expectTransfer(payer, recipient, IERC20(address(buyToken)));
        vm.etch(address(ALLOWANCE_HOLDER), vm.getDeployedCode("AllowanceHolder.sol:AllowanceHolder"));
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(ISettlerActions.TRANSFER_FROM, (recipient, _permit(address(buyToken)), ""));
        vm.expectRevert(abi.encodeWithSelector(ReceivePolicyBlocked.selector, recipient));
        vm.prank(payer);
        ALLOWANCE_HOLDER.exec(
            address(settler),
            address(buyToken),
            1 ether,
            payable(address(settler)),
            abi.encodeCall(settler.execute, (_noSlippage(), actions, bytes32(0)))
        );
    }

    function test_RecipientCheck_MetaTxnTransferFrom_Reverts() public {
        RecipientCheckMetaTxn metaTxn = RecipientCheckMetaTxn(
            payable(deployCode("SettlerRecipientCheck.t.sol:RecipientCheckMetaTxn", abi.encode(recipient, buyToken)))
        );
        metaTxn.expectTransfer(recipient, recipient, IERC20(address(buyToken)));
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(ISettlerActions.METATXN_TRANSFER_FROM, (recipient, _permit(address(buyToken))));
        vm.expectRevert(abi.encodeWithSelector(ReceivePolicyBlocked.selector, recipient));
        metaTxn.executeMetaTxn(_noSlippage(), actions, bytes32(0), recipient, "");
    }

    function test_RecipientCheck_Rfq_Reverts() public {
        settler.expectTransfer(address(this), recipient, IERC20(address(buyToken)));
        _expectBlocked(
            abi.encodeCall(
                ISettlerActions.RFQ,
                (recipient, _permit(address(buyToken)), address(this), "", address(sellToken), 1 ether)
            )
        );
    }

    function test_RecipientCheck_Rfq_MakerPayment_Reverts() public {
        settler.expectTransfer(address(settler), pool, IERC20(address(sellToken)));
        _expectBlocked(
            abi.encodeCall(
                ISettlerActions.RFQ, (recipient, _permit(address(buyToken)), pool, "", address(sellToken), 1 ether)
            )
        );
    }

    function test_RecipientCheck_UniswapV2_PoolPayment_Reverts() public {
        settler.expectTransfer(address(settler), pool, IERC20(address(sellToken)));
        _expectBlocked(
            abi.encodeCall(ISettlerActions.UNISWAPV2, (recipient, address(sellToken), 1_000_000, pool, uint24(0), 0))
        );
    }

    function test_RecipientCheck_Velodrome_PoolPayment_Reverts() public {
        settler.expectTransfer(address(settler), pool, IERC20(address(sellToken)));
        vm.mockCall(
            pool,
            abi.encodeCall(IVelodromePair.metadata, ()),
            abi.encode(1 ether, 1 ether, 100 ether, 100 ether, true, sellToken, buyToken)
        );
        _expectBlocked(abi.encodeCall(ISettlerActions.VELODROME, (recipient, 1_000_000, pool, uint24(1), 0)));
    }

    function test_RecipientCheck_UniswapV3_PoolPayment_UsesSettler() public {
        address v3Pool = _uniV3Pool();
        vm.etch(v3Pool, address(new RecipientCheckV3Pool()).code);
        settler.expectTransfer(address(settler), v3Pool, IERC20(address(sellToken)));
        bytes memory path = abi.encodePacked(address(sellToken), uint8(0), uint24(500), uint160(0), address(buyToken));
        _expectBlocked(abi.encodeCall(ISettlerActions.UNISWAPV3, (recipient, 1_000_000, path, 0)));
    }

    function test_RecipientCheck_UniswapV3VIP_PoolPayment_UsesPayer() public {
        address v3Pool = _uniV3Pool();
        vm.etch(v3Pool, address(new RecipientCheckV3Pool()).code);
        settler.expectTransfer(address(this), v3Pool, IERC20(address(sellToken)));
        bytes memory path = abi.encodePacked(uint8(0), uint24(500), uint160(0), address(buyToken));
        _expectBlocked(
            abi.encodeCall(ISettlerActions.UNISWAPV3_VIP, (recipient, _permit(address(sellToken)), path, "", 0))
        );
    }

    function test_RecipientCheck_UniswapV2_BothDirections_Revert() public {
        settler.expectTransfer(pool, recipient, IERC20(address(buyToken)));
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
        settler.expectTransfer(_uniV3Pool(), recipient, IERC20(address(buyToken)));
        bytes memory path = abi.encodePacked(address(sellToken), uint8(0), uint24(500), uint160(0), address(buyToken));
        _expectBlocked(abi.encodeCall(ISettlerActions.UNISWAPV3, (recipient, 1_000_000, path, 0)));
    }

    function test_RecipientCheck_UniswapV3VIP_Reverts() public {
        settler.expectTransfer(_uniV3Pool(), recipient, IERC20(address(buyToken)));
        bytes memory path = abi.encodePacked(uint8(0), uint24(500), uint160(0), address(buyToken));
        _expectBlocked(
            abi.encodeCall(ISettlerActions.UNISWAPV3_VIP, (recipient, _permit(address(sellToken)), path, "", 0))
        );
    }

    function test_RecipientCheck_Velodrome_BothDirections_Revert() public {
        settler.expectTransfer(pool, recipient, IERC20(address(buyToken)));
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
        settler.expectTransfer(pool, recipient, IERC20(address(buyToken)));
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
        settler.expectTransfer(pool, recipient, IERC20(address(buyToken)));
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
        order.maker_address = makeAddr("maker");
        settler.expectTransfer(order.maker_address, recipient, IERC20(address(buyToken)));
        ISettlerActions.BebopMakerSignature memory signature;
        _expectBlocked(abi.encodeCall(ISettlerActions.BEBOP, (recipient, address(sellToken), order, signature, 0)));
    }

    function test_RecipientCheck_Renegade_Reverts() public {
        address darkpool = makeAddr("darkpool");
        vm.mockCall(
            0xD9E0507D706408D0f14E22e50880189Fd915be80,
            abi.encodeCall(IRenegadeGasSponsor.darkpoolAddress, ()),
            abi.encode(darkpool)
        );
        settler.expectTransfer(darkpool, recipient, IERC20(address(buyToken)));
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
        address blockedRecipient = settler.expectedRecipient();
        vm.expectRevert(abi.encodeWithSelector(ReceivePolicyBlocked.selector, blockedRecipient));
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

    function _uniV3Pool() private view returns (address) {
        (address token0, address token1) = address(sellToken) < address(buyToken)
            ? (address(sellToken), address(buyToken))
            : (address(buyToken), address(sellToken));
        return computeCreate2Address(
            keccak256(abi.encode(token0, token1, uint24(500))), uniswapV3InitHash, uniswapV3BaseFactory
        );
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

    function checkRecipient(address sender, address recipient, IERC20 token) external view {
        _checkRecipient(sender, recipient, token);
    }

    function restrictedTarget(address target) external view returns (bool) {
        return _isRestrictedTarget(target);
    }

    function hasRecipientCheck() external pure returns (bool) {
        return _hasRecipientCheck();
    }
}

contract TempoMetaTxnRecipientCheckHarness is TempoSettlerMetaTxn {
    constructor() TempoSettlerMetaTxn(bytes20(0)) {}

    function checkRecipient(address sender, address recipient, IERC20 token) external view {
        _checkRecipient(sender, recipient, token);
    }

    function restrictedTarget(address target) external view returns (bool) {
        return _isRestrictedTarget(target);
    }

    function hasRecipientCheck() external pure returns (bool) {
        return _hasRecipientCheck();
    }
}

contract TempoIntentRecipientCheckHarness is TempoSettlerIntent {
    constructor() TempoSettlerIntent(bytes20(0)) {}

    function checkRecipient(address sender, address recipient, IERC20 token) external view {
        _checkRecipient(sender, recipient, token);
    }

    function restrictedTarget(address target) external view returns (bool) {
        return _isRestrictedTarget(target);
    }

    function hasRecipientCheck() external pure returns (bool) {
        return _hasRecipientCheck();
    }
}

contract TempoRecipientCheckUnitTest is Test {
    function test_RecipientCheck_Basic_ReceivePolicyRegistry_Reverts() public {
        TempoSettler settler =
            TempoSettler(payable(deployCode("TakerSubmitted.sol:TempoSettler", abi.encode(bytes20(0)))));
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(
            ISettlerActions.BASIC,
            (
                address(0),
                0,
                0x403c000000000000000000000000000000000000,
                0,
                abi.encodeWithSignature("setReceivePolicy(uint64,uint64,address)", uint64(0), uint64(0), address(0))
            )
        );
        vm.expectRevert(ConfusedDeputy.selector);
        settler.execute(ISettlerBase.AllowedSlippage(payable(address(0)), IERC20(address(0)), 0), actions, bytes32(0));
    }

    function test_RecipientCheck_TempoTaker_Enabled() public {
        TempoRecipientCheckHarness settler =
            TempoRecipientCheckHarness(payable(deployCode("SettlerRecipientCheck.t.sol:TempoRecipientCheckHarness")));
        assertTrue(settler.hasRecipientCheck());
        assertTrue(settler.restrictedTarget(0x403c000000000000000000000000000000000000));
        assertTrue(settler.restrictedTarget(0xB10C000000000000000000000000000000000000));
    }

    function test_RecipientCheck_TempoMetaTxn_Enabled() public {
        TempoMetaTxnRecipientCheckHarness settler = TempoMetaTxnRecipientCheckHarness(
            payable(deployCode("SettlerRecipientCheck.t.sol:TempoMetaTxnRecipientCheckHarness"))
        );
        assertTrue(settler.hasRecipientCheck());
        assertTrue(settler.restrictedTarget(0x403c000000000000000000000000000000000000));
        assertTrue(settler.restrictedTarget(0xB10C000000000000000000000000000000000000));
    }

    function test_RecipientCheck_TempoIntent_Enabled() public {
        TempoIntentRecipientCheckHarness settler = TempoIntentRecipientCheckHarness(
            payable(deployCode("SettlerRecipientCheck.t.sol:TempoIntentRecipientCheckHarness"))
        );
        assertTrue(settler.hasRecipientCheck());
        assertTrue(settler.restrictedTarget(0x403c000000000000000000000000000000000000));
        assertTrue(settler.restrictedTarget(0xB10C000000000000000000000000000000000000));
    }
}
