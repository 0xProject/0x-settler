// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {IERC5267} from "src/interfaces/IERC5267.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {Settler} from "src/Settler.sol";
import {SettlerMetaTxn} from "src/SettlerMetaTxn.sol";
import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";
import {SafeTransferLib} from "src/vendor/SafeTransferLib.sol";
import {NativeV2, INativeV2Router} from "src/core/NativeV2.sol";
import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";
import {SettlerMetaTxnPairTest} from "./SettlerMetaTxnPairTest.t.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";


abstract contract NativeV2Test is SettlerMetaTxnPairTest {
    using SafeTransferLib for IERC20;

    bytes32 constant EIP712_DOMAIN_TYPE_HASH =
        keccak256("EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)");

    /// @dev The EIP-712 typeHash for RFQ Quote Widget Authorization.
    bytes32 constant RFQ_QUOTE_WIDGET_SIGNATURE_HASH =
        keccak256("RFQTQuote(bytes32 quote,address widgetFeeRecipient,uint256 widgetFeeRate)");

    /// @dev The EIP-712 typeHash for Market Maker RFQ Quote Authorization.
    bytes32 constant ORDER_SIGNATURE_HASH = keccak256(
        "Order(uint256 nonce,address signer,address buyerToken,address sellerToken,uint256 buyerTokenAmount,uint256 sellerTokenAmount,uint256 deadlineTimestamp,uint256 decayStartTime,uint256 decayExponent,uint256 maxSlippageBps,bytes16 quoteId)"
    );

    INativeV2Router router = INativeV2Router(0x0f9f2366C6157F2aCD3C2bFA45Cd9031c152D2Cf);
    address feeSigner;
    address rfqSigner;
    uint256 feeSignerPk;
    uint256 rfqSignerPk;
    address recipient;

    function nativeV2Pool() internal virtual returns (address);
    function weth() internal virtual returns (IERC20);

    function nativeV2BlockNumber() internal virtual returns (uint256) {
        return 23151204;
    }

    modifier setNativeV2Block() {
        uint256 blockNumber = vm.getBlockNumber();
        vm.rollFork(nativeV2BlockNumber());
        _;
        vm.rollFork(blockNumber);
    }

    function setUp() public virtual override {
        super.setUp();
        if (nativeV2Pool() != address(0)) {
            vm.makePersistent(address(PERMIT2));
            vm.makePersistent(address(allowanceHolder));
            vm.makePersistent(address(settler));
            vm.makePersistent(address(fromToken()));
            vm.makePersistent(address(toToken()));

            vm.label(nativeV2Pool(), "NativeV2Pool");
            vm.label(address(router), "NativeV2Router");
            (feeSigner, feeSignerPk) = makeAddrAndKey("feeSigner");
            (rfqSigner, rfqSignerPk) = makeAddrAndKey("rfqSigner");
            recipient = makeAddr("recipient");
        }
    }

    function _prepareQuote(IERC20 fromToken, IERC20 toToken)
        internal
        returns (INativeV2Router.RFQTQuote memory quote)
    {
        return INativeV2Router.RFQTQuote({
            pool: nativeV2Pool(),
            signer: rfqSigner,
            recipient: recipient,
            sellerToken: address(fromToken),
            buyerToken: address(toToken),
            sellerTokenAmount: amount(),
            buyerTokenAmount: amount(), // 1:1 rate for simplicity
            amountOutMinimum: 0,
            deadlineTimestamp: block.timestamp,
            nonce: uint256(keccak256("test-nonce")),
            decayStartTime: block.timestamp,
            decayExponent: 0, // 0 to avoid decay slippage calculation
            maxSlippageBps: 0,
            quoteId: bytes16(keccak256("test-quote-id")),
            multiHop: false,
            signature: "",
            widgetFee: INativeV2Router.WidgetFee({
                feeRecipient: address(0x1),
                feeRate: 0 // 0% fee
            }),
            widgetFeeSignature: ""
        });
    }

    function testSellToNativeV2() public skipIf(nativeV2Pool() == address(0)) setNativeV2Block {
        _sellToNativeV2WithAllowanceHolder(fromToken(), toToken(), amount(), "allowanceHolder_nativeV2");
        assertEq(toToken().balanceOf(recipient), amount(), "Assets not received");
    }


    function testSellToNativeV2Reverse() public skipIf(nativeV2Pool() == address(0)) setNativeV2Block {
        _sellToNativeV2WithAllowanceHolder(toToken(), fromToken(), amount(), "allowanceHolder_nativeV2_reverse");
        assertEq(fromToken().balanceOf(recipient), amount(), "Assets not received");
    }

    function testSellToNativeV2OverrideQuoteAmount() public skipIf(nativeV2Pool() == address(0)) setNativeV2Block {
        uint256 amount_ = amount() - amount() / 20; // 5% deviation (deviation is allowed below 10%)
        _sellToNativeV2WithAllowanceHolder(fromToken(), toToken(), amount_, "allowanceHolder_nativeV2_override_amount");
        assertEq(toToken().balanceOf(recipient), amount_, "Assets not received");
    }

    function testSellEthToNativeV2() public skipIf(nativeV2Pool() == address(0)) setNativeV2Block {
        _sellToNativeV2WithSettler(IERC20(address(0)), fromToken(), amount(), "settler_nativeV2");
        assertEq(fromToken().balanceOf(recipient), amount(), "Assets not received");
    }

    function testSellToNativeV2MetaTxn() public skipIf(nativeV2Pool() == address(0)) setNativeV2Block {
        _sellToNativeV2WithSettlerMetaTxn(fromToken(), toToken(), amount(), "metaTxn_nativeV2");
        assertEq(toToken().balanceOf(recipient), amount(), "Assets not received");
    }

    function _sellToNativeV2(IERC20 fromToken, IERC20 toToken, uint256 amount_) internal returns (bytes[] memory) {
        INativeV2Router.RFQTQuote memory quote = _prepareQuote(fromToken, toToken);

        // Register signer for router
        // writes to `mapping(address => bool) public signers` at slot 6
        vm.store(address(router), keccak256(abi.encode(feeSigner, uint256(6))), bytes32(uint256(1)));

        // Register rfqSigner for pool
        // writes to `mapping(address => bool) public rfqSigners` at slot 8
        vm.store(nativeV2Pool(), keccak256(abi.encode(quote.signer, uint256(8))), bytes32(uint256(1)));

        // Compute RFQ signature
        (, string memory name, string memory version, uint256 chainId, address verifyingContract,,) =
            IERC5267(nativeV2Pool()).eip712Domain();

        bytes32 domainSeparator = keccak256(
            abi.encode(
                EIP712_DOMAIN_TYPE_HASH, keccak256(bytes(name)), keccak256(bytes(version)), chainId, verifyingContract
            )
        );

        bytes32 rfqDigest = keccak256(
            bytes.concat(
                hex"1901",
                abi.encode(
                    domainSeparator,
                    keccak256(
                        abi.encode(
                            ORDER_SIGNATURE_HASH,
                            quote.nonce,
                            quote.signer,
                            quote.buyerToken == address(0) ? address(weth()) : quote.buyerToken,
                            quote.sellerToken == address(0) ? address(weth()) : quote.sellerToken,
                            quote.buyerTokenAmount,
                            quote.sellerTokenAmount,
                            quote.deadlineTimestamp,
                            quote.decayStartTime,
                            quote.decayExponent,
                            quote.maxSlippageBps,
                            quote.quoteId
                        )
                    )
                )
            )
        );

        (uint8 v, bytes32 r, bytes32 s) = vm.sign(rfqSignerPk, rfqDigest);
        quote.signature = abi.encodePacked(r, s, v);

        // Compute fee signature
        (, name, version, chainId, verifyingContract,,) = IERC5267(address(router)).eip712Domain();

        domainSeparator = keccak256(
            abi.encode(
                EIP712_DOMAIN_TYPE_HASH, keccak256(bytes(name)), keccak256(bytes(version)), chainId, verifyingContract
            )
        );

        bytes32 quoteDigest = keccak256(
            bytes.concat(
                hex"1901",
                abi.encode(
                    domainSeparator,
                    keccak256(
                        abi.encode(
                            RFQ_QUOTE_WIDGET_SIGNATURE_HASH,
                            keccak256( // quoteHash
                                abi.encode(
                                    quote.pool,
                                    quote.recipient,
                                    quote.sellerToken,
                                    quote.buyerToken,
                                    quote.sellerTokenAmount,
                                    quote.buyerTokenAmount,
                                    quote.deadlineTimestamp,
                                    quote.decayStartTime,
                                    quote.decayExponent,
                                    quote.maxSlippageBps,
                                    quote.multiHop,
                                    quote.signature
                                )
                            ),
                            quote.widgetFee.feeRecipient,
                            quote.widgetFee.feeRate
                        )
                    )
                )
            )
        );

        (v, r, s) = vm.sign(feeSignerPk, quoteDigest);
        quote.widgetFeeSignature = abi.encodePacked(r, s, v);

        // Prepare Settler actions
        return ActionDataBuilder.build(
            // Perform a transfer into Settler via AllowanceHolder
            abi.encodeCall(
                ISettlerActions.TRANSFER_FROM,
                (
                    address(settler),
                    defaultERC20PermitTransfer(address(fromToken), amount_, 0 /* nonce */ ),
                    new bytes(0) /* sig (empty) */
                )
            ),
            // Execute NativeV2 from the Settler balance
            abi.encodeCall(
                ISettlerActions.NATIVEV2, (address(router), 10_000, abi.encode(quote, uint256(0), uint256(0)))
            )
        );
    }

    function _sellToNativeV2WithAllowanceHolder(IERC20 fromToken, IERC20 toToken, uint256 amount_, string memory name_)
        internal
    {
        bytes[] memory actions = _sellToNativeV2(fromToken, toToken, amount_);

        deal(address(fromToken), address(this), amount_);
        fromToken.safeApprove(address(allowanceHolder), amount_);

        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;

        snapStartName(name_);
        _allowanceHolder.exec(
            address(_settler),
            address(fromToken),
            amount(),
            payable(address(_settler)),
            abi.encodeCall(
                _settler.execute,
                (
                    ISettlerBase.AllowedSlippage({
                        recipient: payable(address(0)),
                        buyToken: IERC20(address(0)),
                        minAmountOut: 0 ether
                    }),
                    actions,
                    bytes32(0)
                )
            )
        );
        snapEnd();
    }

    function _sellToNativeV2WithSettler(IERC20 fromToken, IERC20 toToken, uint256 amount_, string memory name_)
        internal
    {
        assertEq(address(fromToken), address(0), "fromToken expected to be ETH");
        // use only the NATIVEV2 action
        bytes[] memory actions = ActionDataBuilder.build(_sellToNativeV2(fromToken, toToken, amount_)[1]);

        deal(address(this), amount_);
        deal(address(settler), 0); // for some reason settler has 1 wei

        Settler _settler = settler;

        snapStartName(name_);
        _settler.execute{value: amount_}(
            ISettlerBase.AllowedSlippage({
                recipient: payable(address(0)),
                buyToken: IERC20(address(0)),
                minAmountOut: 0 ether
            }),
            actions,
            bytes32(0)
        );
        snapEnd();
    }

    function _sellToNativeV2WithSettlerMetaTxn(IERC20 fromToken, IERC20 toToken, uint256 amount_, string memory name_)
        internal
    {
        bytes[] memory actions = _sellToNativeV2(fromToken, toToken, amount_);

        // override permit data
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken), amount_, uint256(keccak256("permit-nonce")));
        actions[0] = abi.encodeCall(
            ISettlerActions.METATXN_TRANSFER_FROM,
            (address(settlerMetaTxn), permit)
        );

        ISettlerBase.AllowedSlippage memory allowedSlippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(0)),
            buyToken: IERC20(address(0)),
            minAmountOut: 0 ether
        });

        bytes32[] memory actionHashes = new bytes32[](actions.length);
        for (uint256 i; i < actionHashes.length; i++) {
            actionHashes[i] = keccak256(actions[i]);
        }
        bytes32 actionsHash = keccak256(abi.encodePacked(actionHashes));
        bytes32 witness = keccak256(
            abi.encode(
                SLIPPAGE_AND_ACTIONS_TYPEHASH,
                allowedSlippage.recipient,
                allowedSlippage.buyToken,
                allowedSlippage.minAmountOut,
                actionsHash
            )
        );
        bytes memory sig = getPermitWitnessTransferSignature(
            permit, address(settlerMetaTxn), FROM_PRIVATE_KEY, FULL_PERMIT2_WITNESS_TYPEHASH, witness, permit2Domain
        );

        SettlerMetaTxn _settlerMetaTxn = settlerMetaTxn;
        vm.etch(FROM, bytes(""));

        vm.startPrank(address(this), address(this));
        snapStartName(name_);
        _settlerMetaTxn.executeMetaTxn(
            ISettlerBase.AllowedSlippage({
                recipient: payable(address(0)),
                buyToken: IERC20(address(0)),
                minAmountOut: 0 ether
            }),
            actions,
            bytes32(0),
            FROM,
            sig
        );
        snapEnd();
        vm.stopPrank();
    }
}
