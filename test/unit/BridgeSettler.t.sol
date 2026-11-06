// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ALLOWANCE_HOLDER} from "src/allowanceholder/IAllowanceHolder.sol";
import {BridgeSettler, BridgeSettlerBase} from "src/bridge/BridgeSettler.sol";
import {ISettlerTakerSubmitted} from "src/interfaces/ISettlerTakerSubmitted.sol";
import {MainnetSettler} from "src/chains/Mainnet/TakerSubmitted.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {IBridgeSettlerActions} from "src/bridge/IBridgeSettlerActions.sol";
import {DAI, USDC, USDT, USDD} from "src/core/MakerPSM.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {Utils} from "./Utils.sol";
import {DEPLOYER} from "src/deployer/DeployerAddress.sol";
import {IERC721View} from "src/deployer/IDeployer.sol";
import {MockERC20} from "@solmate/test/utils/mocks/MockERC20.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {Permit2Signature} from "../utils/Permit2Signature.sol";
import {DeployPermit2} from "lib/permit2/test/utils/DeployPermit2.sol";
import {RfqOrderSettlement} from "src/core/RfqOrderSettlement.sol";

contract BridgeSettlerDummy is BridgeSettler {
    constructor(bytes20 gitCommit) BridgeSettlerBase(gitCommit) {}
}

contract BridgeDummy {
    function take(address token, uint256 amount) external {
        IERC20(token).transferFrom(msg.sender, address(this), amount);
    }

    receive() external payable {}
}

contract BridgeSettlerTestBase is Test {
    BridgeSettler bridgeSettler;
    ISettlerTakerSubmitted settler;
    IERC20 token;
    BridgeDummy bridgeDummy;

    function _testBridgeSettler() internal virtual {
        bridgeSettler = new BridgeSettlerDummy(bytes20(0));
    }

    function setUp() public virtual {
        _testBridgeSettler();
        vm.label(address(bridgeSettler), "BridgeSettler");
        bridgeDummy = new BridgeDummy();
        token = IERC20(address(new MockERC20("Test Token", "TT", 18)));
    }

    function _getDefaultTransferFrom(address token_, uint256 amount) internal returns (bytes memory) {
        return _getDefaultTransferFrom(address(bridgeSettler), token_, amount);
    }

    function _getSettlerDefaultTransferFrom(address token_, uint256 amount) internal returns (bytes memory) {
        return _getDefaultTransferFrom(address(settler), token_, amount);
    }

    function _getDefaultTransferFrom(address settler_, address token_, uint256 amount) internal returns (bytes memory) {
        return abi.encodeCall(
            ISettlerActions.TRANSFER_FROM,
            (
                address(settler_),
                ISignatureTransfer.PermitTransferFrom({
                    permitted: ISignatureTransfer.TokenPermissions({token: address(token_), amount: amount}),
                    nonce: 0,
                    deadline: block.timestamp
                }),
                bytes("")
            )
        );
    }
}

contract BridgeSettlerUnitTest is BridgeSettlerTestBase {
    function setUp() public virtual override {
        super.setUp();

        vm.etch(address(ALLOWANCE_HOLDER), vm.getDeployedCode("AllowanceHolder.sol:AllowanceHolder"));
        // Mock DAI, USDC, USDT, and USDD for MainnetSettler to be usable
        deployCodeTo("MockERC20", abi.encode("DAI", "DAI", 18), address(DAI));
        deployCodeTo("MockERC20", abi.encode("USDC", "USDC", 6), address(USDC));
        deployCodeTo("MockERC20", abi.encode("USDT", "USDT", 6), address(USDT));
        deployCodeTo("MockERC20", abi.encode("USDD", "USDD", 18), address(USDD));
        settler = new MainnetSettler(bytes20(0));
    }
}

contract BridgeSettlerTest is BridgeSettlerUnitTest, Utils {
    function testUserFlow() public {
        address user = makeAddr("user");
        uint256 amount = 2000;

        // 1. Take the assets from BridgeSettler
        // 2. And just send them back to BridgeSettler
        bytes[] memory settlerActions = ActionDataBuilder.build(
            _getSettlerDefaultTransferFrom(address(token), amount),
            abi.encodeCall(
                ISettlerActions.BASIC,
                (
                    address(token),
                    1_000_000,
                    address(token),
                    0x24,
                    abi.encodeCall(IERC20.transfer, (address(bridgeSettler), 0))
                )
            )
        );

        // 1. Take the assets from the BridgeSettler
        // 2. Do a swap (that just takes and returns the assets)
        // 3. Bridge the assets to the dummy bridge
        bytes[] memory bridgeActions = ActionDataBuilder.build(
            _getDefaultTransferFrom(address(token), amount),
            abi.encodeCall(
                IBridgeSettlerActions.SETTLER_SWAP,
                (
                    address(token),
                    amount,
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
            ),
            abi.encodeCall(
                IBridgeSettlerActions.BASIC,
                (
                    address(token),
                    1_000_000,
                    address(bridgeDummy),
                    0x24,
                    abi.encodeCall(BridgeDummy.take, (address(token), 0))
                )
            )
        );

        vm.prank(user);
        token.approve(address(ALLOWANCE_HOLDER), type(uint256).max);
        deal(address(token), user, amount);

        _mockExpectCall(address(DEPLOYER), abi.encodeCall(IERC721View.ownerOf, (2)), abi.encode(address(settler)));
        vm.expectCall(
            address(token), abi.encodeCall(IERC20.transferFrom, (address(bridgeSettler), address(settler), amount))
        );
        vm.expectCall(address(token), abi.encodeCall(IERC20.transfer, (address(bridgeSettler), amount - 1)));
        vm.prank(user);
        ALLOWANCE_HOLDER.exec(
            address(bridgeSettler),
            address(token),
            amount,
            payable(address(bridgeSettler)),
            abi.encodeCall(BridgeSettler.execute, (bridgeActions, bytes32(0)))
        );

        // first use: Settler and BridgeSettler each keep 1 wei
        assertEq(token.balanceOf(address(bridgeDummy)), amount - 2, "Bridge did not receive the assets");
        assertEq(token.balanceOf(address(settler)), 1);
        assertEq(token.balanceOf(address(bridgeSettler)), 1);
    }

    function testUserFlowWithNative() public {
        address user = makeAddr("user");
        address ETH_ADDRESS = address(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE);
        uint256 amount = 1000;

        // 1. Just send Native back to BridgeSettler
        bytes[] memory settlerActions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.BASIC, (ETH_ADDRESS, 1_000_000, address(bridgeSettler), 0x00, bytes("")))
        );

        // 1. Do a swap (that just takes and returns the assets)
        // 2. Bridge the assets to the dummy bridge
        bytes[] memory bridgeActions = ActionDataBuilder.build(
            abi.encodeCall(
                IBridgeSettlerActions.SETTLER_SWAP,
                (
                    ETH_ADDRESS,
                    amount,
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
            ),
            abi.encodeCall(IBridgeSettlerActions.BASIC, (ETH_ADDRESS, 1_000_000, address(bridgeDummy), 0, bytes("")))
        );

        deal(user, amount);

        _mockExpectCall(address(DEPLOYER), abi.encodeCall(IERC721View.ownerOf, (2)), abi.encode(address(settler)));
        vm.prank(user);
        bridgeSettler.execute{value: amount}(bridgeActions, bytes32(0));

        assertEq(address(bridgeDummy).balance, amount, "Bridge did not receive the assets");
    }
}

contract BridgeSettlerRfqTest is BridgeSettlerUnitTest, Permit2Signature, DeployPermit2 {
    uint256 internal constant MAKER_PRIVATE_KEY = 0x0ff1c1a1;
    address internal MAKER = vm.addr(MAKER_PRIVATE_KEY);
    uint256 internal constant MAKER_NONCE = 1;
    bytes32 internal constant CONSIDERATION_TYPEHASH =
        keccak256("Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)");
    bytes32 internal constant RFQ_PERMIT2_WITNESS_TYPEHASH = keccak256(
        "PermitWitnessTransferFrom(TokenPermissions permitted,address spender,uint256 nonce,uint256 deadline,Consideration consideration)Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)TokenPermissions(address token,uint256 amount)"
    );
    bytes4 internal constant INVALID_SIGNER_SELECTOR = bytes4(keccak256("InvalidSigner()"));
    address internal constant ETH_ADDRESS = 0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE;

    ISignatureTransfer internal permit2;
    IERC20 internal buyToken;
    address internal user;
    uint256 internal constant SELL_AMOUNT = 2000;
    uint256 internal constant BUY_AMOUNT = 1 ether;

    function setUp() public override {
        super.setUp();
        permit2 = ISignatureTransfer(deployPermit2());
        buyToken = IERC20(address(new MockERC20("Buy Token", "BT", 18)));
        user = makeAddr("user");

        deal(address(token), user, SELL_AMOUNT);
        vm.prank(user);
        token.approve(address(ALLOWANCE_HOLDER), type(uint256).max);

        deal(address(buyToken), MAKER, BUY_AMOUNT);
        vm.prank(MAKER);
        buyToken.approve(address(permit2), type(uint256).max);
    }

    function _makerNonceUsed() internal view returns (bool) {
        return permit2.nonceBitmap(MAKER, MAKER_NONCE >> 8) & (1 << uint8(MAKER_NONCE)) != 0;
    }

    // The maker quotes `BUY_AMOUNT` of `buyToken` for `SELL_AMOUNT` of `token`, bound to `taker` and spendable
    // only by `spender`.
    function _makerQuote(address taker, address spender)
        internal
        view
        returns (ISignatureTransfer.PermitTransferFrom memory makerPermit, bytes memory makerSig)
    {
        makerPermit = defaultERC20PermitTransfer(address(buyToken), BUY_AMOUNT, MAKER_NONCE);
        bytes32 witness = keccak256(
            bytes.concat(
                CONSIDERATION_TYPEHASH,
                abi.encode(
                    RfqOrderSettlement.Consideration({
                        token: token, amount: SELL_AMOUNT, counterparty: taker, partialFillAllowed: true
                    })
                )
            )
        );
        makerSig = getPermitWitnessTransferSignature(
            makerPermit, spender, MAKER_PRIVATE_KEY, RFQ_PERMIT2_WITNESS_TYPEHASH, witness, permit2.DOMAIN_SEPARATOR()
        );
    }

    function _rfqAction(ISignatureTransfer.PermitTransferFrom memory makerPermit, bytes memory makerSig)
        internal
        view
        returns (bytes memory)
    {
        return abi.encodeCall(
            IBridgeSettlerActions.RFQ,
            (address(bridgeSettler), makerPermit, MAKER, makerSig, address(token), SELL_AMOUNT)
        );
    }

    function _executeThroughAllowanceHolder(address taker, uint256 amount, bytes[] memory bridgeActions) internal {
        vm.prank(taker);
        ALLOWANCE_HOLDER.exec(
            address(bridgeSettler),
            address(token),
            amount,
            payable(address(bridgeSettler)),
            abi.encodeCall(BridgeSettler.execute, (bridgeActions, bytes32(0)))
        );
    }

    function testRfq() public {
        (ISignatureTransfer.PermitTransferFrom memory makerPermit, bytes memory makerSig) =
            _makerQuote(user, address(bridgeSettler));

        // 1. Take the assets from the user
        // 2. Fill the maker's quote, paying the maker from BridgeSettler
        // 3. Bridge the maker's assets to the dummy bridge
        bytes[] memory bridgeActions = ActionDataBuilder.build(
            _getDefaultTransferFrom(address(token), SELL_AMOUNT),
            _rfqAction(makerPermit, makerSig),
            abi.encodeCall(
                IBridgeSettlerActions.BASIC,
                (
                    address(buyToken),
                    1_000_000,
                    address(bridgeDummy),
                    0x24,
                    abi.encodeCall(BridgeDummy.take, (address(buyToken), 0))
                )
            )
        );

        vm.expectCall(address(token), abi.encodeCall(IERC20.transfer, (MAKER, SELL_AMOUNT)));
        vm.expectCall(
            address(buyToken), abi.encodeCall(IERC20.transferFrom, (MAKER, address(bridgeSettler), BUY_AMOUNT))
        );
        _executeThroughAllowanceHolder(user, SELL_AMOUNT, bridgeActions);

        assertTrue(_makerNonceUsed());
        assertEq(token.balanceOf(user), 0);
        assertEq(token.balanceOf(MAKER), SELL_AMOUNT);
        assertEq(buyToken.balanceOf(MAKER), 0);
        // first use: BridgeSettler keeps 1 wei
        assertEq(buyToken.balanceOf(address(bridgeDummy)), BUY_AMOUNT - 1, "Bridge did not receive the assets");
        assertEq(buyToken.balanceOf(address(bridgeSettler)), 1);
    }

    function testRfqReuseByOtherSenderReverts() public {
        (ISignatureTransfer.PermitTransferFrom memory makerPermit, bytes memory makerSig) =
            _makerQuote(user, address(bridgeSettler));
        address attacker = makeAddr("attacker");

        // Zero fill: the attacker brings no taker token
        bytes[] memory bridgeActions = ActionDataBuilder.build(_rfqAction(makerPermit, makerSig));
        vm.prank(attacker);
        vm.expectRevert(INVALID_SIGNER_SELECTOR);
        bridgeSettler.execute(bridgeActions, bytes32(0));
        assertFalse(_makerNonceUsed());

        // Dust fill: the attacker brings one base unit of taker token
        deal(address(token), attacker, 1);
        vm.prank(attacker);
        token.approve(address(ALLOWANCE_HOLDER), type(uint256).max);
        bridgeActions =
            ActionDataBuilder.build(_getDefaultTransferFrom(address(token), 1), _rfqAction(makerPermit, makerSig));
        vm.expectRevert(INVALID_SIGNER_SELECTOR);
        _executeThroughAllowanceHolder(attacker, 1, bridgeActions);
        assertFalse(_makerNonceUsed());

        // The user's own transaction still fills
        bridgeActions = ActionDataBuilder.build(
            _getDefaultTransferFrom(address(token), SELL_AMOUNT), _rfqAction(makerPermit, makerSig)
        );
        _executeThroughAllowanceHolder(user, SELL_AMOUNT, bridgeActions);
        assertTrue(_makerNonceUsed());
        assertEq(token.balanceOf(MAKER), SELL_AMOUNT);
        assertEq(buyToken.balanceOf(address(bridgeSettler)), BUY_AMOUNT);
    }

    function testRfqReuseThroughSettlerReverts() public {
        (ISignatureTransfer.PermitTransferFrom memory makerPermit, bytes memory makerSig) =
            _makerQuote(user, address(bridgeSettler));
        address attacker = makeAddr("attacker");

        // The same action nested in a Settler call names a different Permit2 spender
        bytes[] memory settlerActions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.RFQ, (address(settler), makerPermit, MAKER, makerSig, address(token), SELL_AMOUNT)
            )
        );
        bytes[] memory bridgeActions = ActionDataBuilder.build(
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

        vm.mockCall(address(DEPLOYER), abi.encodeCall(IERC721View.ownerOf, (2)), abi.encode(address(settler)));
        vm.prank(attacker);
        vm.expectRevert(INVALID_SIGNER_SELECTOR);
        bridgeSettler.execute(bridgeActions, bytes32(0));
        assertFalse(_makerNonceUsed());
    }
}
