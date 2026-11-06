// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {BridgeSettlerTestBase} from "../unit/BridgeSettler.t.sol";
import {MainnetDefaultFork} from "./BaseForkTest.t.sol";
import {IDeployer} from "src/deployer/IDeployer.sol";
import {DEPLOYER} from "src/deployer/DeployerAddress.sol";
import {ISettlerTakerSubmitted} from "src/interfaces/ISettlerTakerSubmitted.sol";
import {MainnetBridgeSettler} from "src/chains/Mainnet/BridgeSettler.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {IBridgeSettlerActions} from "src/bridge/IBridgeSettlerActions.sol";
import {BridgeSettler} from "src/bridge/BridgeSettler.sol";
import {ALLOWANCE_HOLDER} from "src/allowanceholder/IAllowanceHolder.sol";
import {RfqOrderSettlement} from "src/core/RfqOrderSettlement.sol";
import {PERMIT2} from "src/core/Permit2Payment.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {Permit2Signature} from "../utils/Permit2Signature.sol";

abstract contract BridgeSettlerIntegrationTest is BridgeSettlerTestBase, MainnetDefaultFork {
    function _testBlockNumber() internal pure virtual override returns (uint256) {
        return 22719835;
    }

    function _testBridgeSettler() internal virtual override {
        bridgeSettler = new MainnetBridgeSettler(bytes20(0));
    }

    function setUp() public virtual override {
        // deploy BridgeSettler
        super.setUp();
        vm.createSelectFork(_testChainId(), _testBlockNumber());
        vm.setEvmVersion("osaka");
        settler = ISettlerTakerSubmitted(IDeployer(DEPLOYER).ownerOf(2));
        vm.label(address(settler), "Settler");
    }
}

contract BridgeSettlerRfqIntegrationTest is BridgeSettlerIntegrationTest, Permit2Signature {
    IERC20 internal constant WETH = IERC20(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2);
    IERC20 internal constant USDC = IERC20(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48);
    address internal constant ETH_ADDRESS = 0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE;

    uint256 internal constant MAKER_PRIVATE_KEY = 0x0ff1c1a1;
    address internal MAKER = vm.addr(MAKER_PRIVATE_KEY);
    uint256 internal constant MAKER_NONCE = 1;
    bytes32 internal constant CONSIDERATION_TYPEHASH =
        keccak256("Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)");
    bytes32 internal constant RFQ_PERMIT2_WITNESS_TYPEHASH = keccak256(
        "PermitWitnessTransferFrom(TokenPermissions permitted,address spender,uint256 nonce,uint256 deadline,Consideration consideration)Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)TokenPermissions(address token,uint256 amount)"
    );
    bytes4 internal constant INVALID_SIGNER_SELECTOR = bytes4(keccak256("InvalidSigner()"));

    uint256 internal constant USDC_AMOUNT = 2_000e6;
    uint256 internal constant WETH_AMOUNT = 1 ether;

    address internal user;
    address internal bridge;

    function setUp() public override {
        super.setUp();
        user = makeAddr("user");
        bridge = makeAddr("bridge");
        vm.label(MAKER, "Maker");

        deal(address(USDC), MAKER, USDC_AMOUNT);
        deal(address(WETH), MAKER, WETH_AMOUNT);
        vm.startPrank(MAKER);
        USDC.approve(address(PERMIT2), type(uint256).max);
        WETH.approve(address(PERMIT2), type(uint256).max);
        vm.stopPrank();
    }

    function _makerNonceUsed() internal view returns (bool) {
        return PERMIT2.nonceBitmap(MAKER, MAKER_NONCE >> 8) & (1 << uint8(MAKER_NONCE)) != 0;
    }

    function _makerQuote(
        IERC20 makerToken,
        uint256 makerAmount,
        IERC20 takerToken,
        uint256 takerAmount,
        address taker,
        address spender
    ) internal view returns (ISignatureTransfer.PermitTransferFrom memory makerPermit, bytes memory makerSig) {
        makerPermit = defaultERC20PermitTransfer(address(makerToken), makerAmount, MAKER_NONCE);
        bytes32 witness = keccak256(
            bytes.concat(
                CONSIDERATION_TYPEHASH,
                abi.encode(
                    RfqOrderSettlement.Consideration({
                        token: takerToken, amount: takerAmount, counterparty: taker, partialFillAllowed: true
                    })
                )
            )
        );
        makerSig = getPermitWitnessTransferSignature(
            makerPermit, spender, MAKER_PRIVATE_KEY, RFQ_PERMIT2_WITNESS_TYPEHASH, witness, PERMIT2.DOMAIN_SEPARATOR()
        );
    }

    function _bridgeAction(IERC20 bridgeToken) internal view returns (bytes memory) {
        return abi.encodeCall(
            IBridgeSettlerActions.BASIC,
            (address(bridgeToken), 1_000_000, address(bridgeToken), 0x24, abi.encodeCall(IERC20.transfer, (bridge, 0)))
        );
    }

    function _executeThroughAllowanceHolder(address taker, IERC20 sellToken, uint256 amount, bytes[] memory actions)
        internal
    {
        vm.prank(taker);
        ALLOWANCE_HOLDER.exec(
            address(bridgeSettler),
            address(sellToken),
            amount,
            payable(address(bridgeSettler)),
            abi.encodeCall(BridgeSettler.execute, (actions, bytes32(0)))
        );
    }

    function testRfqErc20() public {
        deal(address(USDC), user, USDC_AMOUNT);
        vm.prank(user);
        USDC.approve(address(ALLOWANCE_HOLDER), type(uint256).max);
        (ISignatureTransfer.PermitTransferFrom memory makerPermit, bytes memory makerSig) =
            _makerQuote(WETH, WETH_AMOUNT, USDC, USDC_AMOUNT, user, address(bridgeSettler));

        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultTransferFrom(address(USDC), USDC_AMOUNT),
            abi.encodeCall(
                IBridgeSettlerActions.RFQ,
                (address(bridgeSettler), makerPermit, MAKER, makerSig, address(USDC), USDC_AMOUNT)
            ),
            _bridgeAction(WETH)
        );
        _executeThroughAllowanceHolder(user, USDC, USDC_AMOUNT, actions);

        assertTrue(_makerNonceUsed());
        assertEq(USDC.balanceOf(user), 0);
        assertEq(USDC.balanceOf(MAKER), 2 * USDC_AMOUNT);
        assertEq(WETH.balanceOf(MAKER), 0);
        // first use: BridgeSettler keeps 1 wei
        assertEq(WETH.balanceOf(bridge), WETH_AMOUNT - 1);
        assertEq(WETH.balanceOf(address(bridgeSettler)), 1);
    }

    function testRfqNative() public {
        deal(user, WETH_AMOUNT);
        (ISignatureTransfer.PermitTransferFrom memory makerPermit, bytes memory makerSig) =
            _makerQuote(USDC, USDC_AMOUNT, WETH, WETH_AMOUNT, user, address(bridgeSettler));

        // 1. Wrap the user's ETH
        // 2. Fill the maker's quote with the WETH
        // 3. Bridge the USDC
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(IBridgeSettlerActions.BASIC, (ETH_ADDRESS, 1_000_000, address(WETH), 0, bytes(""))),
            abi.encodeCall(
                IBridgeSettlerActions.RFQ,
                (address(bridgeSettler), makerPermit, MAKER, makerSig, address(WETH), WETH_AMOUNT)
            ),
            _bridgeAction(USDC)
        );
        vm.prank(user);
        bridgeSettler.execute{value: WETH_AMOUNT}(actions, bytes32(0));

        assertTrue(_makerNonceUsed());
        assertEq(user.balance, 0);
        assertEq(WETH.balanceOf(MAKER), 2 * WETH_AMOUNT);
        assertEq(USDC.balanceOf(MAKER), 0);
        assertEq(USDC.balanceOf(bridge), USDC_AMOUNT - 1);
        assertEq(USDC.balanceOf(address(bridgeSettler)), 1);
    }

    function testRfqReuseByOtherSenderReverts() public {
        (ISignatureTransfer.PermitTransferFrom memory makerPermit, bytes memory makerSig) =
            _makerQuote(USDC, USDC_AMOUNT, WETH, WETH_AMOUNT, user, address(bridgeSettler));
        bytes memory rfq = abi.encodeCall(
            IBridgeSettlerActions.RFQ,
            (address(bridgeSettler), makerPermit, MAKER, makerSig, address(WETH), WETH_AMOUNT)
        );
        address attacker = makeAddr("attacker");

        // Zero fill
        bytes[] memory actions = ActionDataBuilder.build(rfq);
        vm.prank(attacker);
        vm.expectRevert(INVALID_SIGNER_SELECTOR);
        bridgeSettler.execute(actions, bytes32(0));
        assertFalse(_makerNonceUsed());

        // Dust fill
        deal(address(WETH), attacker, 1);
        vm.prank(attacker);
        WETH.approve(address(ALLOWANCE_HOLDER), type(uint256).max);
        actions = ActionDataBuilder.build(_getDefaultTransferFrom(address(WETH), 1), rfq);
        vm.expectRevert(INVALID_SIGNER_SELECTOR);
        _executeThroughAllowanceHolder(attacker, WETH, 1, actions);
        assertFalse(_makerNonceUsed());

        // The same signature nested in the live Settler names a different Permit2 spender
        bytes[] memory settlerActions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.RFQ, (address(settler), makerPermit, MAKER, makerSig, address(WETH), WETH_AMOUNT)
            )
        );
        actions = ActionDataBuilder.build(
            abi.encodeCall(
                IBridgeSettlerActions.SETTLER_SWAP,
                (
                    ETH_ADDRESS,
                    0,
                    address(settler),
                    abi.encodeCall(
                        ISettlerTakerSubmitted.execute,
                        (
                            ISettlerBase.AllowedSlippage({
                                recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
                            }),
                            settlerActions,
                            bytes32(0)
                        )
                    )
                )
            )
        );
        vm.prank(attacker);
        vm.expectRevert(INVALID_SIGNER_SELECTOR);
        bridgeSettler.execute(actions, bytes32(0));
        assertFalse(_makerNonceUsed());

        // The user's own transaction still fills
        deal(user, WETH_AMOUNT);
        actions = ActionDataBuilder.build(
            abi.encodeCall(IBridgeSettlerActions.BASIC, (ETH_ADDRESS, 1_000_000, address(WETH), 0, bytes(""))), rfq
        );
        vm.prank(user);
        bridgeSettler.execute{value: WETH_AMOUNT}(actions, bytes32(0));
        assertTrue(_makerNonceUsed());
        assertEq(WETH.balanceOf(MAKER), 2 * WETH_AMOUNT);
        assertEq(USDC.balanceOf(address(bridgeSettler)), USDC_AMOUNT);
    }
}
