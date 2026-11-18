// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {Vm} from "@forge-std/Vm.sol";
import {BridgeSettlerIntegrationTest} from "./BridgeSettler.t.sol";
import {ALLOWANCE_HOLDER} from "src/allowanceholder/IAllowanceHolder.sol";
import {IBridgeSettlerActions} from "src/bridge/IBridgeSettlerActions.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {ISettlerTakerSubmitted} from "src/interfaces/ISettlerTakerSubmitted.sol";
import {BnbBridgeSettler} from "src/chains/Bnb/BridgeSettler.sol";
import {IXBridge} from "src/core/XBridge.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {LibBytes} from "../utils/LibBytes.sol";

interface IXBridgeAdmin {
    error DestinationChainNotAllowlisted(uint64 destinationChainSelector);
    error EnforcedPause();
    error InsufficientMessageValue(uint256 value, uint256 fee);

    event MessageSent(
        bytes32 indexed messageId,
        uint64 indexed destinationChainSelector,
        bytes32 receiver,
        bytes32 tokenReceiver,
        uint64 tokenId,
        uint256 sharesAmount
    );

    function custodyWallet() external view returns (address);
    function owner() external view returns (address);
    function pause() external;
}

interface IXStock is IERC20 {
    event TransferShares(address indexed from, address indexed to, uint256 value);

    function getUnderlyingAmountByShares(uint256) external view returns (uint256);
    function sharesOf(address) external view returns (uint256);
    function multiplier() external view returns (uint256);
    function getSharesByUnderlyingAmount(uint256) external view returns (uint256);
}

abstract contract XBridgeTestBase is BridgeSettlerIntegrationTest {
    using LibBytes for bytes;

    address constant XBRIDGE = 0x9eC0e4A4c411493773E01e2ABF4D42395788846b;

    IXStock constant TSLAX = IXStock(0x8aD3c73F833d3F9A523aB01476625F269aEB7Cf0);

    // CCIP chain selectors (https://docs.chain.link/ccip/directory/mainnet)
    uint64 constant ETHEREUM_SELECTOR = 5009297550715157269;
    uint64 constant ARBITRUM_SELECTOR = 4949039107694359620;
    uint64 constant SOLANA_SELECTOR = 124615329519749607;
    uint64 constant BASE_SELECTOR = 15971525489660198786;

    bytes32 recipient;
    address custody;

    function setUp() public virtual override {
        super.setUp();
        vm.label(XBRIDGE, "xBridge");
        vm.label(address(TSLAX), "TSLAx");
        recipient = bytes32(uint256(uint160(makeAddr("recipient"))));
        custody = IXBridgeAdmin(XBRIDGE).custodyWallet();
        // The deploy address of the test BridgeSettler can hold stray native on a fork.
        vm.deal(address(bridgeSettler), 0);
    }

    function _fund(IXStock token, uint256 amount) internal {
        vm.prank(custody);
        token.transfer(address(this), amount);
        token.approve(address(ALLOWANCE_HOLDER), amount);
    }

    function _bridgeAction(IERC20 token, uint64 dstSel, bytes memory chainSpecificArgs)
        internal
        view
        returns (bytes memory)
    {
        // The amount is 0 because the action overrides it with BridgeSettler's balance.
        return abi.encodeCall(
            IBridgeSettlerActions.BRIDGE_TO_XBRIDGE,
            (abi.encodeCall(IXBridge.send, (dstSel, recipient, address(token), 0, chainSpecificArgs)).popSelector())
        );
    }

    function _exec(IERC20 sellToken, uint256 sellAmount, uint256 value, bytes[] memory actions) internal {
        ALLOWANCE_HOLDER.exec{value: value}(
            address(bridgeSettler),
            address(sellToken),
            sellAmount,
            payable(address(bridgeSettler)),
            abi.encodeCall(bridgeSettler.execute, (actions, bytes32(0)))
        );
    }

    /// @dev Checks, from the logs of one execution, that BridgeSettler bridged its whole balance,
    /// that custody received exactly the shares in the one `MessageSent`, and that the message names
    /// the expected destination and receiver. Shares that leave for anyone but custody, such as a
    /// fee, must leave before the bridge. `Transfer` logs the requested amount, but balances move
    /// in whole shares, so the shares are counted from `TransferShares`.
    function _checkBridged(IXStock token, uint64 dstSel, uint256 custodySharesBefore) internal {
        Vm.Log[] memory logs = vm.getRecordedLogs();
        uint256 receivedShares;
        uint256 bridgedShares;
        uint256 spentShares;
        uint256 messageShares;
        uint256 messages;
        for (uint256 i; i < logs.length; i++) {
            if (logs[i].emitter == address(token) && logs[i].topics[0] == IXStock.TransferShares.selector) {
                address from = address(uint160(uint256(logs[i].topics[1])));
                address to = address(uint160(uint256(logs[i].topics[2])));
                if (to == address(bridgeSettler)) receivedShares += abi.decode(logs[i].data, (uint256));
                if (from == address(bridgeSettler)) {
                    if (to == custody) bridgedShares += abi.decode(logs[i].data, (uint256));
                    else spentShares += abi.decode(logs[i].data, (uint256));
                }
            } else if (logs[i].emitter == XBRIDGE && logs[i].topics[0] == IXBridgeAdmin.MessageSent.selector) {
                assertEq(uint64(uint256(logs[i].topics[2])), dstSel, "MessageSent destination");
                bytes32 tokenReceiver;
                (, tokenReceiver,, messageShares) = abi.decode(logs[i].data, (bytes32, bytes32, uint64, uint256));
                assertEq(tokenReceiver, recipient, "MessageSent receiver");
                messages++;
            }
        }
        assertEq(messages, 1, "MessageSent not emitted exactly once");
        assertGt(receivedShares, 0, "BridgeSettler received nothing");
        uint256 balance = token.getUnderlyingAmountByShares(receivedShares - spentShares);
        assertEq(messageShares, token.getSharesByUnderlyingAmount(balance), "did not bridge the whole balance");
        assertEq(bridgedShares, messageShares, "custody received != message shares");
        assertEq(token.sharesOf(custody) - custodySharesBefore, messageShares, "custody shares");
        assertEq(
            token.balanceOf(address(bridgeSettler)),
            token.getUnderlyingAmountByShares(receivedShares - spentShares - bridgedShares),
            "BridgeSettler kept more than rounding dust"
        );
    }

    /// @dev Bridges an xStock straight from the taker and checks that all the native sent goes to
    /// xBridge, which keeps what is above the fee.
    function _bridgeFromTaker(IXStock token, uint256 amount, uint64 dstSel, bytes memory chainSpecificArgs) internal {
        _fund(token, amount);
        uint256 fee = IXBridge(XBRIDGE).getDeliveryFeeCost(dstSel, recipient, address(token), amount, chainSpecificArgs);
        uint256 value = fee * 110 / 100;
        deal(address(this), value);

        uint256 custodySharesBefore = token.sharesOf(custody);
        uint256 xBridgeNativeBefore = XBRIDGE.balance;
        assertEq(token.balanceOf(address(bridgeSettler)), 0);

        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultTransferFrom(address(token), amount), _bridgeAction(token, dstSel, chainSpecificArgs)
        );

        // A transfer moves whole shares, so BridgeSettler can end up with slightly less than the
        // taker sent.
        uint256 received = token.getUnderlyingAmountByShares(token.getSharesByUnderlyingAmount(amount));
        vm.expectCall(
            XBRIDGE,
            value,
            abi.encodeCall(IXBridge.send, (dstSel, recipient, address(token), received, chainSpecificArgs))
        );
        vm.recordLogs();
        _exec(token, amount, value, actions);

        _checkBridged(token, dstSel, custodySharesBefore);
        assertEq(address(this).balance, 0, "taker native balance");
        assertEq(address(bridgeSettler).balance, 0, "BridgeSettler native balance");
        // xBridge forwards the fee to the CCIP router and keeps the rest.
        assertEq(XBRIDGE.balance, xBridgeNativeBefore + value - fee, "xBridge native balance");
    }
}

contract XBridgeMainnetTest is XBridgeTestBase {
    IERC20 constant USDC = IERC20(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48);
    IXStock constant SPYX = IXStock(0x90A2a4c76b5D8c0bc892A69EA28Aa775a8f2dD48);
    // Multiplier 0.1e18 at the test block
    IXStock constant ENHAX = IXStock(0xe75AfF5123D9De91A1c27167C6C01B1f5b1eAb14);
    // Multiplier about 10.03e18 at the test block
    IXStock constant KLACX = IXStock(0xb7e2E3eF9F5c6b72a162FFc76382e4477A44D913);

    function _testBlockNumber() internal pure override returns (uint256) {
        return 26439900;
    }

    function testBridgeToArbitrum() public {
        _bridgeFromTaker(TSLAX, 1.234567890123456789e18, ARBITRUM_SELECTOR, "");
    }

    function testBridgeMultiplierBelowOne() public {
        assertEq(ENHAX.multiplier(), 0.1e18);
        _bridgeFromTaker(ENHAX, 12.345678901234567891e18, ARBITRUM_SELECTOR, "");
    }

    function testBridgeMultiplierAboveOne() public {
        assertGt(KLACX.multiplier(), 10e18);
        _bridgeFromTaker(KLACX, 1.234567890123456789e18, ARBITRUM_SELECTOR, "");
    }

    function testBridgeToSolana() public {
        // Writable-account bitmap and the 11 accounts that the receiving program needs, copied from
        // the ETH to Solana send in transaction
        // 0xa2d63fd32c06477eda36ac6ce74f929e6beb70eaa5f891d8676e0756a032099e
        bytes32[] memory accounts = new bytes32[](11);
        accounts[0] = 0x4b662b2cb13c54da7db33181385169df183c3515ce0278793f39dba34ed50542;
        accounts[1] = 0x24f9d357338f06eefc29dcf41f60aa7cd65bb17247609fc03b2b24f5306a7182;
        accounts[2] = 0xb9a619e5382c52b6623edfeca646b74160292146d171a698f74f842fee17dadd;
        accounts[3] = 0x51956418821a040b82ec633c023b3481aa8b1565c0983e44cfbe29c0178f59a3;
        accounts[4] = 0x7391e49e83b48fcc93105c0ffb4fb6bc41b399c3dc71a90d34084ce6e47060cb;
        accounts[5] = 0x07e8dc2cde7b23a0d743f8f1276b657d8a9eea06950ba67a8d3033c53c4cde4f;
        accounts[6] = 0x06ddf6e1ee758fde18425dbce46ccddab61afc4d83b90d27febdf928d8a18bfc;
        accounts[7] = 0x74dcc5bd02f4f20d7b2729d1eb996b5e1a8c1aabd30f23c216479f7484da0405;
        accounts[8] = 0xd98beedd765b53132c8d04b735275e699081a78f0b368b9d1c50bf49fcac0ba2;
        accounts[9] = 0x9cca73189d85631cde18afae0e4dbd03c2aa1413cf42e385758d0ce2808c6aa5;
        accounts[10] = 0x6699892655bfaf368f98c884a5d805a11d68ca1d960ff1c85c1a9a48542c8b19;
        recipient = 0x6699892655bfaf368f98c884a5d805a11d68ca1d960ff1c85c1a9a48542c8b19;
        _bridgeFromTaker(SPYX, 1.234567890123456789e18, SOLANA_SELECTOR, abi.encode(uint64(0x304), accounts));
    }

    /// @dev Sells USDC for TSLAx in Settler, then bridges whatever TSLAx arrives.
    function testSwapThenBridge() public {
        // Uniswap V3 TSLAx/USDC 0.3% pool
        address pool = 0xA7fd774E0aD54A6D2CeAfB4103615f473E589cC6;
        vm.label(pool, "TSLAx/USDC");
        uint256 sellAmount = 20e6;
        deal(address(USDC), address(this), sellAmount);
        USDC.approve(address(ALLOWANCE_HOLDER), sellAmount);

        bytes[] memory swapActions = ActionDataBuilder.build(
            _getSettlerDefaultTransferFrom(address(USDC), sellAmount),
            abi.encodeCall(
                ISettlerActions.UNISWAPV3,
                (
                    address(settler),
                    1_000_000,
                    abi.encodePacked(
                        USDC, uint8(0), uint24(3000), uint160(1461446703485210103287273052203988822378723970341), TSLAX
                    ),
                    0
                )
            )
        );
        bytes memory swap = abi.encodeCall(
            IBridgeSettlerActions.SETTLER_SWAP,
            (
                address(USDC),
                sellAmount,
                address(settler),
                abi.encodeCall(
                    ISettlerTakerSubmitted.execute,
                    (
                        ISettlerBase.AllowedSlippage({
                            recipient: payable(address(bridgeSettler)), buyToken: TSLAX, minAmountOut: 1
                        }),
                        swapActions,
                        bytes32(0)
                    )
                )
            )
        );

        // The fee doesn't depend on the amount, so it can be quoted before the swap output is known.
        uint256 fee = IXBridge(XBRIDGE).getDeliveryFeeCost(ARBITRUM_SELECTOR, recipient, address(TSLAX), 1, "");
        uint256 value = fee * 110 / 100;
        deal(address(this), value);
        uint256 custodySharesBefore = TSLAX.sharesOf(custody);
        uint256 xBridgeNativeBefore = XBRIDGE.balance;

        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultTransferFrom(address(USDC), sellAmount), swap, _bridgeAction(TSLAX, ARBITRUM_SELECTOR, "")
        );
        vm.recordLogs();
        _exec(USDC, sellAmount, value, actions);

        // The bridged amount is whatever Settler paid out, which the quote couldn't know.
        _checkBridged(TSLAX, ARBITRUM_SELECTOR, custodySharesBefore);
        assertEq(USDC.balanceOf(address(this)), 0, "taker USDC");
        assertEq(address(this).balance, 0, "taker native balance");
        assertEq(address(bridgeSettler).balance, 0, "BridgeSettler native balance");
        assertEq(XBRIDGE.balance, xBridgeNativeBefore + value - fee, "xBridge native balance");
    }

    /// @dev A fee `BASIC` before the action. The bridged amount follows from the token's share
    /// rounding, which a quote has to replay.
    function testFeeThenBridge() public {
        IXStock token = KLACX;
        uint256 amount = 1.234567890123456789e18;
        uint256 feePpm = 1_000;
        address feeRecipient = makeAddr("feeRecipient");
        _fund(token, amount);
        uint256 fee = IXBridge(XBRIDGE).getDeliveryFeeCost(ARBITRUM_SELECTOR, recipient, address(token), amount, "");
        deal(address(this), fee);

        // `BASIC` takes its share of the spendable balance, which is the balance minus 1 wei.
        uint256 shares = token.getSharesByUnderlyingAmount(amount);
        uint256 feeAmount = (token.getUnderlyingAmountByShares(shares) - 1) * feePpm / 1_000_000;
        uint256 feeShares = token.getSharesByUnderlyingAmount(feeAmount);
        uint256 expected = token.getUnderlyingAmountByShares(shares - feeShares);
        uint256 custodySharesBefore = token.sharesOf(custody);

        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultTransferFrom(address(token), amount),
            abi.encodeCall(
                IBridgeSettlerActions.BASIC,
                (address(token), feePpm, address(token), 0x24, abi.encodeCall(IERC20.transfer, (feeRecipient, 0)))
            ),
            _bridgeAction(token, ARBITRUM_SELECTOR, "")
        );
        vm.expectCall(
            XBRIDGE, fee, abi.encodeCall(IXBridge.send, (ARBITRUM_SELECTOR, recipient, address(token), expected, ""))
        );
        vm.recordLogs();
        _exec(token, amount, fee, actions);

        _checkBridged(token, ARBITRUM_SELECTOR, custodySharesBefore);
        assertEq(token.sharesOf(feeRecipient), feeShares, "fee shares");
    }

    function testRevertBelowFee() public {
        uint256 amount = 1e18;
        _fund(TSLAX, amount);
        uint256 fee = IXBridge(XBRIDGE).getDeliveryFeeCost(ARBITRUM_SELECTOR, recipient, address(TSLAX), amount, "");
        deal(address(this), fee - 1);

        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultTransferFrom(address(TSLAX), amount), _bridgeAction(TSLAX, ARBITRUM_SELECTOR, "")
        );
        vm.expectRevert(abi.encodeWithSelector(IXBridgeAdmin.InsufficientMessageValue.selector, fee - 1, fee));
        _exec(TSLAX, amount, fee - 1, actions);
    }

    function testRevertDestinationNotAllowlisted() public {
        uint256 amount = 1e18;
        _fund(TSLAX, amount);
        deal(address(this), 1 ether);

        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultTransferFrom(address(TSLAX), amount), _bridgeAction(TSLAX, BASE_SELECTOR, "")
        );
        vm.expectRevert(abi.encodeWithSelector(IXBridgeAdmin.DestinationChainNotAllowlisted.selector, BASE_SELECTOR));
        _exec(TSLAX, amount, 1 ether, actions);
    }

    function testRevertPaused() public {
        vm.prank(IXBridgeAdmin(XBRIDGE).owner());
        IXBridgeAdmin(XBRIDGE).pause();

        uint256 amount = 1e18;
        _fund(TSLAX, amount);
        deal(address(this), 1 ether);

        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultTransferFrom(address(TSLAX), amount), _bridgeAction(TSLAX, ARBITRUM_SELECTOR, "")
        );
        vm.expectRevert(IXBridgeAdmin.EnforcedPause.selector);
        _exec(TSLAX, amount, 1 ether, actions);
    }
}

contract XBridgeBnbTest is XBridgeTestBase {
    function _testBridgeSettler() internal override {
        bridgeSettler = new BnbBridgeSettler(bytes20(0));
    }

    function _testChainId() internal pure override returns (string memory) {
        return "bnb";
    }

    function _testBlockNumber() internal pure override returns (uint256) {
        return 134257600;
    }

    function testBridgeToEthereum() public {
        _bridgeFromTaker(TSLAX, 1.234567890123456789e18, ETHEREUM_SELECTOR, "");
    }
}
