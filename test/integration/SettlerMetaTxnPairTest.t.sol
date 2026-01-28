// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";

import {SettlerBasePairTest, Shim} from "./SettlerBasePairTest.t.sol";
import {ICurveV2Pool} from "./vendor/ICurveV2Pool.sol";
import {IZeroEx} from "./vendor/IZeroEx.sol";

import {LibBytes} from "../utils/LibBytes.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";

import {SafeTransferLib} from "src/vendor/SafeTransferLib.sol";

import {MainnetSettlerMetaTxn as SettlerMetaTxn} from "src/chains/Mainnet/MetaTxn.sol";
import {Settler} from "src/Settler.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {RfqOrderSettlement} from "src/core/RfqOrderSettlement.sol";

import {MainnetDefaultFork} from "./BaseForkTest.t.sol";

abstract contract SettlerMetaTxnPairTest is SettlerBasePairTest {
    using SafeTransferLib for IERC20;
    using LibBytes for bytes;

    SettlerMetaTxn internal settlerMetaTxn;

    function settlerMetaTxnInitCode() internal virtual returns (bytes memory) {
        return bytes.concat(type(SettlerMetaTxn).creationCode, abi.encode(bytes20(0)));
    }

    function _deploySettlerMetaTxn() private returns (SettlerMetaTxn r) {
        bytes memory initCode = settlerMetaTxnInitCode();
        assembly ("memory-safe") {
            r := create(0x00, add(0x20, initCode), mload(initCode))
            if iszero(r) { revert(0x00, 0x00) }
        }
    }

    function setUp() public virtual override {
        super.setUp();

        uint256 forkChainId = (new Shim()).chainId();
        vm.chainId(31337);
        // Preserve the settlerMetaTxn address for the hardcoded signing hash.
        new NonceBump();
        settlerMetaTxn = _deploySettlerMetaTxn();
        vm.chainId(forkChainId);

        // ### Taker ###
        safeApproveIfBelow(fromToken(), FROM, address(PERMIT2), amount());

        // ### Maker / Seller ###
        // Rfq inside of Settler
        safeApproveIfBelow(toToken(), MAKER, address(PERMIT2), amount());

        warmPermit2Nonce(FROM);
        warmPermit2Nonce(MAKER);
    }

    function uniswapV3Path() internal virtual returns (bytes memory);

    /// @dev Performs an direct RFQ trade between MAKER and FROM
    // Funds are transferred MAKER->FROM and FROM->MAKER
    function testSettler_rfq() public skipIf(true) { // action `RFQ_VIP` is disabled
        ISignatureTransfer.PermitTransferFrom memory makerPermit =
            defaultERC20PermitTransfer(address(toToken()), amount(), PERMIT2_MAKER_NONCE);
        ISignatureTransfer.PermitTransferFrom memory takerPermit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), PERMIT2_FROM_NONCE);

        RfqOrderSettlement.Consideration memory makerConsideration = RfqOrderSettlement.Consideration({
            token: fromToken(),
            amount: amount(),
            counterparty: FROM,
            partialFillAllowed: false
        });

        bytes32 makerWitness = keccak256(bytes.concat(CONSIDERATION_TYPEHASH, abi.encode(makerConsideration)));
        bytes memory makerSig = getPermitWitnessTransferSignature(
            makerPermit, address(settler), MAKER_PRIVATE_KEY, RFQ_PERMIT2_WITNESS_TYPEHASH, makerWitness, permit2Domain
        );

        bytes memory takerSig =
            getPermitTransferSignature(takerPermit, address(settler), FROM_PRIVATE_KEY, permit2Domain);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.RFQ_VIP, (FROM, takerPermit, makerPermit, MAKER, makerSig, takerSig))
        );

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_rfq");
        _settler.execute(
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

    bytes32 internal constant FULL_PERMIT2_WITNESS_TYPEHASH = keccak256(
        "PermitWitnessTransferFrom(TokenPermissions permitted,address spender,uint256 nonce,uint256 deadline,SlippageAndActions slippageAndActions)SlippageAndActions(address recipient,address buyToken,uint256 minAmountOut,bytes[] actions)TokenPermissions(address token,uint256 amount)"
    );
    bytes32 internal constant SLIPPAGE_AND_ACTIONS_TYPEHASH =
        keccak256("SlippageAndActions(address recipient,address buyToken,uint256 minAmountOut,bytes[] actions)");

    function testSettler_metaTxn_uniswapV3() public skipIf(uniswapV3Path().length == 0) {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), PERMIT2_FROM_NONCE);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.METATXN_TRANSFER_FROM, (address(settlerMetaTxn), permit)),
            abi.encodeCall(ISettlerActions.UNISWAPV3, (FROM, 10_000, uniswapV3Path(), 0))
        );

        bytes32[] memory actionHashes = new bytes32[](actions.length);
        for (uint256 i; i < actionHashes.length; i++) {
            actionHashes[i] = keccak256(actions[i]);
        }
        bytes32 actionsHash = keccak256(abi.encodePacked(actionHashes));
        bytes32 witness =
            keccak256(abi.encode(SLIPPAGE_AND_ACTIONS_TYPEHASH, address(0), address(0), 0 ether, actionsHash));
        bytes memory sig = getPermitWitnessTransferSignature(
            permit, address(settlerMetaTxn), FROM_PRIVATE_KEY, FULL_PERMIT2_WITNESS_TYPEHASH, witness, permit2Domain
        );

        SettlerMetaTxn _settlerMetaTxn = settlerMetaTxn;
        // Submitted by third party
        vm.startPrank(address(this), address(this)); // does a `call` to keep the optimizer from reordering opcodes
        snapStartName("settler_metaTxn_uniswapV3");
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
    }

    function testSettler_metaTxn_uniswapV3VIP() public skipIf(uniswapV3Path().length == 0) {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), PERMIT2_FROM_NONCE);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.METATXN_UNISWAPV3_VIP, (FROM, permit, uniswapV3Path(), 0))
        );

        bytes32[] memory actionHashes = new bytes32[](actions.length);
        for (uint256 i; i < actionHashes.length; i++) {
            actionHashes[i] = keccak256(actions[i]);
        }
        bytes32 actionsHash = keccak256(abi.encodePacked(actionHashes));
        bytes32 witness =
            keccak256(abi.encode(SLIPPAGE_AND_ACTIONS_TYPEHASH, address(0), address(0), 0 ether, actionsHash));
        bytes memory sig = getPermitWitnessTransferSignature(
            permit, address(settlerMetaTxn), FROM_PRIVATE_KEY, FULL_PERMIT2_WITNESS_TYPEHASH, witness, permit2Domain
        );

        SettlerMetaTxn _settlerMetaTxn = settlerMetaTxn;
        // Submitted by third party
        vm.startPrank(address(this), address(this)); // does a `call` to keep the optimizer from reordering opcodes
        snapStartName("settler_metaTxn_uniswapV3VIP");
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
    }

    function testSettler_metaTxn_rfq() public skipIf(true) { // action `METATXN_RFQ_VIP` is disabled
        ISignatureTransfer.PermitTransferFrom memory makerPermit =
            defaultERC20PermitTransfer(address(toToken()), amount(), PERMIT2_MAKER_NONCE);
        ISignatureTransfer.PermitTransferFrom memory takerPermit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), PERMIT2_FROM_NONCE);

        RfqOrderSettlement.Consideration memory makerConsideration = RfqOrderSettlement.Consideration({
            token: fromToken(),
            amount: amount(),
            counterparty: FROM,
            partialFillAllowed: false
        });
        bytes32 makerWitness = keccak256(bytes.concat(CONSIDERATION_TYPEHASH, abi.encode(makerConsideration)));
        bytes memory makerSig = getPermitWitnessTransferSignature(
            makerPermit,
            address(settlerMetaTxn),
            MAKER_PRIVATE_KEY,
            RFQ_PERMIT2_WITNESS_TYPEHASH,
            makerWitness,
            permit2Domain
        );

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.METATXN_RFQ_VIP, (FROM, takerPermit, makerPermit, MAKER, makerSig))
        );
        bytes32[] memory actionHashes = new bytes32[](actions.length);
        for (uint256 i; i < actionHashes.length; i++) {
            actionHashes[i] = keccak256(actions[i]);
        }
        bytes32 actionsHash = keccak256(abi.encodePacked(actionHashes));
        bytes32 takerWitness =
            keccak256(abi.encode(SLIPPAGE_AND_ACTIONS_TYPEHASH, address(0), address(0), 0 ether, actionsHash));

        bytes memory takerSig = getPermitWitnessTransferSignature(
            takerPermit,
            address(settlerMetaTxn),
            FROM_PRIVATE_KEY,
            FULL_PERMIT2_WITNESS_TYPEHASH,
            takerWitness,
            permit2Domain
        );

        SettlerMetaTxn _settlerMetaTxn = settlerMetaTxn;
        // Submitted by third party
        vm.startPrank(address(this), address(this)); // does a `call` to keep the optimizer from reordering opcodes
        snapStartName("settler_metaTxn_rfq");
        _settlerMetaTxn.executeMetaTxn(
            ISettlerBase.AllowedSlippage({
                recipient: payable(address(0)),
                buyToken: IERC20(address(0)),
                minAmountOut: 0 ether
            }),
            actions,
            bytes32(0),
            FROM,
            takerSig
        );
        snapEnd();
    }

    /// @dev Performs a direct RFQ trade between MAKER and FROM but with Settler receiving the sell and buy token funds.
    /// Funds transfer
    ///   RFQ
    ///     TAKER->Settler
    ///     MAKER->Settler
    ///     Settler->MAKER
    ///   TRANSFER_OUT_PROPORTIONAL
    ///     Settler->FEE_RECIPIENT
    ///   SLIPPAGE
    ///     Settler->FROM
    function testSettler_rfq_fee_full_custody() public {
        ISignatureTransfer.PermitTransferFrom memory makerPermit = ISignatureTransfer.PermitTransferFrom({
            permitted: ISignatureTransfer.TokenPermissions({token: address(toToken()), amount: amount()}),
            nonce: PERMIT2_MAKER_NONCE,
            deadline: block.timestamp + 100
        });
        RfqOrderSettlement.Consideration memory makerConsideration = RfqOrderSettlement.Consideration({
            token: fromToken(),
            amount: amount(),
            counterparty: FROM,
            partialFillAllowed: true
        });
        bytes32 makerWitness = keccak256(bytes.concat(CONSIDERATION_TYPEHASH, abi.encode(makerConsideration)));
        bytes memory makerSig = getPermitWitnessTransferSignature(
            makerPermit, address(settler), MAKER_PRIVATE_KEY, RFQ_PERMIT2_WITNESS_TYPEHASH, makerWitness, permit2Domain
        );

        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(
                ISettlerActions.RFQ, (address(settler), makerPermit, MAKER, makerSig, address(fromToken()), amount())
            ),
            abi.encodeCall(
                ISettlerActions.BASIC,
                (
                    address(toToken()),
                    1_000,
                    address(toToken()),
                    0x24,
                    abi.encodeCall(toToken().transfer, (BURN_ADDRESS, 0))
                )
            )
        );

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_rfq_fee_full_custody");
        _settler.execute(
            ISettlerBase.AllowedSlippage({recipient: FROM, buyToken: toToken(), minAmountOut: amount() * 9_000 / 10_000}),
            actions,
            bytes32(0)
        );
        snapEnd();
    }

    function testSettler_eip712hash_hardcoded()
        public
        skipIf(address(fromToken()) != 0x6B175474E89094C44Da98b954EedeAC495271d0F)
        skipIf(toToken() != WETH)
    {
        vm.makePersistent(address(settlerMetaTxn));
        vm.createSelectFork(_testChainId(), MainnetDefaultFork._testBlockNumber());
        vm.setEvmVersion("cancun");
        deal(address(fromToken()), FROM, amount());
        vm.prank(FROM);
        require(fromToken().approve(address(PERMIT2), type(uint256).max));

        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), PERMIT2_FROM_NONCE);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.METATXN_TRANSFER_FROM, (address(settlerMetaTxn), permit))
        );

        bytes32[] memory actionHashes = new bytes32[](actions.length);
        for (uint256 i; i < actionHashes.length; i++) {
            actionHashes[i] = keccak256(actions[i]);
        }
        bytes32 actionsHash = keccak256(abi.encodePacked(actionHashes));
        bytes32 witness =
            keccak256(abi.encode(SLIPPAGE_AND_ACTIONS_TYPEHASH, FROM, address(fromToken()), amount(), actionsHash));
        bytes memory sig = getPermitWitnessTransferSignature(
            permit, address(settlerMetaTxn), FROM_PRIVATE_KEY, FULL_PERMIT2_WITNESS_TYPEHASH, witness, permit2Domain
        );

        /// WARNING *** WARNING *** WARNING *** WARNING *** WARNING *** WARNING *** WARNING *** WARNING
        /// WARNING                                                                             WARNING
        /// WARNING           DO NOT CHANGE THIS HASH VALUE WITHOUT CONTACTING JACOB            WARNING
        /// WARNING              THIS HASH VALUE IS COPIED INTO A TEST IN SOLVER                WARNING
        /// WARNING           YOU WILL BREAK THE BUILD IF YOU DO NOT SYNCHRONIZE THEM           WARNING
        /// WARNING                                                                             WARNING
        /// WARNING *** WARNING *** WARNING *** WARNING *** WARNING *** WARNING *** WARNING *** WARNING
        bytes32 signingHash = bytes32(0xbf1b86e7987783db15e7b7f414a1f0c7972ab305fdbb062895896c4a5aa0fc86);
        /// WARNING *** WARNING *** WARNING *** WARNING *** WARNING *** WARNING *** WARNING *** WARNING

        uint8 v;
        bytes32 r;
        bytes32 s;
        assembly ("memory-safe") {
            v := mload(add(0x41, sig))
            r := mload(add(0x20, sig))
            s := mload(add(0x40, sig))
        }

        vm.expectCall(address(0x01), abi.encode(signingHash, v, r, s));
        settlerMetaTxn.executeMetaTxn(
            ISettlerBase.AllowedSlippage({recipient: FROM, buyToken: fromToken(), minAmountOut: amount()}),
            actions,
            bytes32(0),
            FROM,
            sig
        );
    }
}

contract NonceBump {}
