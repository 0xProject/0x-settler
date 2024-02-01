// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {IERC20} from "../../src/IERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";
import {ICurveV2Pool} from "./vendor/ICurveV2Pool.sol";
import {IZeroEx} from "./vendor/IZeroEx.sol";

import {LibBytes} from "../utils/LibBytes.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";

import {SafeTransferLib} from "../../src/utils/SafeTransferLib.sol";

import {AllowanceHolder} from "../../src/AllowanceHolder.sol";
import {Settler} from "../../src/Settler.sol";
import {ISettlerActions} from "../../src/ISettlerActions.sol";
import {OtcOrderSettlement} from "../../src/core/OtcOrderSettlement.sol";

abstract contract SettlerMetaTxnPairTest is SettlerBasePairTest {
    using SafeTransferLib for IERC20;
    using LibBytes for bytes;

    function setUp() public virtual override {
        super.setUp();
        // ### Taker ###
        safeApproveIfBelow(fromToken(), FROM, address(PERMIT2), amount());

        // ### Maker / Seller ###
        // Otc inside of Settler
        safeApproveIfBelow(toToken(), MAKER, address(PERMIT2), amount());

        warmPermit2Nonce(FROM);
        warmPermit2Nonce(MAKER);
    }

    function uniswapV3Path() internal virtual returns (bytes memory);

    /// @dev Performs an direct OTC trade between MAKER and FROM
    // Funds are transferred MAKER->FROM and FROM->MAKER
    function testSettler_otc() public {
        ISignatureTransfer.PermitTransferFrom memory makerPermit =
            defaultERC20PermitTransfer(address(toToken()), amount(), PERMIT2_MAKER_NONCE);
        ISignatureTransfer.PermitTransferFrom memory takerPermit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), PERMIT2_FROM_NONCE);

        OtcOrderSettlement.Consideration memory makerConsideration = OtcOrderSettlement.Consideration({
            token: address(fromToken()),
            amount: amount(),
            counterparty: FROM,
            partialFillAllowed: false
        });

        bytes32 makerWitness = keccak256(bytes.concat(CONSIDERATION_TYPEHASH, abi.encode(makerConsideration)));
        bytes memory makerSig = getPermitWitnessTransferSignature(
            makerPermit, address(settler), MAKER_PRIVATE_KEY, OTC_PERMIT2_WITNESS_TYPEHASH, makerWitness, permit2Domain
        );

        bytes memory takerSig =
            getPermitTransferSignature(takerPermit, address(settler), FROM_PRIVATE_KEY, permit2Domain);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.SETTLER_OTC_PERMIT2, (FROM, makerPermit, MAKER, makerSig, takerPermit, takerSig)
            )
        );

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_otc");
        _settler.execute(
            actions, Settler.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0 ether})
        );
        snapEnd();
    }

    bytes32 private constant FULL_PERMIT2_WITNESS_TYPEHASH = keccak256(
        "PermitWitnessTransferFrom(TokenPermissions permitted,address spender,uint256 nonce,uint256 deadline,ActionsAndSlippage actionsAndSlippage)ActionsAndSlippage(address buyToken,address recipient,uint256 minAmountOut,bytes[] actions)TokenPermissions(address token,uint256 amount)"
    );
    bytes32 private constant ACTIONS_AND_SLIPPAGE_TYPEHASH =
        keccak256("ActionsAndSlippage(address buyToken,address recipient,uint256 minAmountOut,bytes[] actions)");

    function testSettler_metaTxn_uniswapV3() public {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), PERMIT2_FROM_NONCE);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.METATXN_PERMIT2_TRANSFER_FROM, (address(settler), permit)),
            abi.encodeCall(ISettlerActions.UNISWAPV3_SWAP_EXACT_IN, (FROM, 10_000, 0, uniswapV3Path()))
        );

        bytes32[] memory actionHashes = new bytes32[](actions.length);
        for (uint256 i; i < actionHashes.length; i++) {
            actionHashes[i] = keccak256(actions[i]);
        }
        bytes32 actionsHash = keccak256(abi.encodePacked(actionHashes));
        bytes32 witness =
            keccak256(abi.encode(ACTIONS_AND_SLIPPAGE_TYPEHASH, address(0), address(0), 0 ether, actionsHash));
        bytes memory sig = getPermitWitnessTransferSignature(
            permit, address(settler), FROM_PRIVATE_KEY, FULL_PERMIT2_WITNESS_TYPEHASH, witness, permit2Domain
        );

        Settler _settler = settler;
        // Submitted by third party
        vm.startPrank(address(this), address(this)); // does a `call` to keep the optimizer from reordering opcodes
        snapStartName("settler_metaTxn_uniswapV3");
        _settler.executeMetaTxn(
            actions,
            Settler.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0 ether}),
            FROM,
            sig
        );
        snapEnd();
    }

    function testSettler_metaTxn_uniswapV3VIP() public {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), PERMIT2_FROM_NONCE);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.METATXN_UNISWAPV3_PERMIT2_SWAP_EXACT_IN, (FROM, amount(), 0, uniswapV3Path(), permit)
            )
        );

        bytes32[] memory actionHashes = new bytes32[](actions.length);
        for (uint256 i; i < actionHashes.length; i++) {
            actionHashes[i] = keccak256(actions[i]);
        }
        bytes32 actionsHash = keccak256(abi.encodePacked(actionHashes));
        bytes32 witness =
            keccak256(abi.encode(ACTIONS_AND_SLIPPAGE_TYPEHASH, address(0), address(0), 0 ether, actionsHash));
        bytes memory sig = getPermitWitnessTransferSignature(
            permit, address(settler), FROM_PRIVATE_KEY, FULL_PERMIT2_WITNESS_TYPEHASH, witness, permit2Domain
        );

        Settler _settler = settler;
        // Submitted by third party
        vm.startPrank(address(this), address(this)); // does a `call` to keep the optimizer from reordering opcodes
        snapStartName("settler_metaTxn_uniswapV3VIP");
        _settler.executeMetaTxn(
            actions,
            Settler.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0 ether}),
            FROM,
            sig
        );
        snapEnd();
    }

    function testSettler_metaTxn_otc() public {
        ISignatureTransfer.PermitTransferFrom memory makerPermit =
            defaultERC20PermitTransfer(address(toToken()), amount(), PERMIT2_MAKER_NONCE);
        ISignatureTransfer.PermitTransferFrom memory takerPermit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), PERMIT2_FROM_NONCE);

        OtcOrderSettlement.Consideration memory makerConsideration = OtcOrderSettlement.Consideration({
            token: address(fromToken()),
            amount: amount(),
            counterparty: FROM,
            partialFillAllowed: false
        });
        bytes32 makerWitness = keccak256(bytes.concat(CONSIDERATION_TYPEHASH, abi.encode(makerConsideration)));
        bytes memory makerSig = getPermitWitnessTransferSignature(
            makerPermit, address(settler), MAKER_PRIVATE_KEY, OTC_PERMIT2_WITNESS_TYPEHASH, makerWitness, permit2Domain
        );

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.METATXN_SETTLER_OTC_PERMIT2, (FROM, makerPermit, MAKER, makerSig, takerPermit)
            )
        );
        bytes32[] memory actionHashes = new bytes32[](actions.length);
        for (uint256 i; i < actionHashes.length; i++) {
            actionHashes[i] = keccak256(actions[i]);
        }
        bytes32 actionsHash = keccak256(abi.encodePacked(actionHashes));
        bytes32 takerWitness =
            keccak256(abi.encode(ACTIONS_AND_SLIPPAGE_TYPEHASH, address(0), address(0), 0 ether, actionsHash));

        bytes memory takerSig = getPermitWitnessTransferSignature(
            takerPermit, address(settler), FROM_PRIVATE_KEY, FULL_PERMIT2_WITNESS_TYPEHASH, takerWitness, permit2Domain
        );

        Settler _settler = settler;
        // Submitted by third party
        vm.startPrank(address(this), address(this)); // does a `call` to keep the optimizer from reordering opcodes
        snapStartName("settler_metaTxn_otc");
        _settler.executeMetaTxn(
            actions,
            Settler.AllowedSlippage({buyToken: address(0), recipient: address(0), minAmountOut: 0 ether}),
            FROM,
            takerSig
        );
        snapEnd();
    }

    /// @dev Performs a direct OTC trade between MAKER and FROM but with Settler receiving the sell and buy token funds.
    /// Funds transfer
    ///   OTC
    ///     TAKER->Settler
    ///     MAKER->Settler
    ///     Settler->MAKER
    ///   TRANSFER_OUT_PROPORTIONAL
    ///     Settler->FEE_RECIPIENT
    ///   SLIPPAGE
    ///     Settler->FROM
    function testSettler_otc_fee_full_custody() public {
        ISignatureTransfer.PermitTransferFrom memory makerPermit = ISignatureTransfer.PermitTransferFrom({
            permitted: ISignatureTransfer.TokenPermissions({token: address(toToken()), amount: amount()}),
            nonce: PERMIT2_MAKER_NONCE,
            deadline: block.timestamp + 100
        });
        OtcOrderSettlement.Consideration memory makerConsideration = OtcOrderSettlement.Consideration({
            token: address(fromToken()),
            amount: amount(),
            counterparty: FROM,
            partialFillAllowed: true
        });
        bytes32 makerWitness = keccak256(bytes.concat(CONSIDERATION_TYPEHASH, abi.encode(makerConsideration)));
        bytes memory makerSig = getPermitWitnessTransferSignature(
            makerPermit, address(settler), MAKER_PRIVATE_KEY, OTC_PERMIT2_WITNESS_TYPEHASH, makerWitness, permit2Domain
        );

        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(
                ISettlerActions.SETTLER_OTC_SELF_FUNDED,
                (address(settler), makerPermit, MAKER, makerSig, address(fromToken()), amount())
            ),
            abi.encodeCall(
                ISettlerActions.BASIC_SELL,
                (
                    address(toToken()),
                    address(toToken()),
                    1_000,
                    0x24,
                    abi.encodeCall(toToken().transfer, (BURN_ADDRESS, 0))
                )
            )
        );

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_otc_fee_full_custody");
        _settler.execute(
            actions,
            Settler.AllowedSlippage({
                buyToken: address(toToken()),
                recipient: FROM,
                minAmountOut: amount() * 9_000 / 10_000
            })
        );
        snapEnd();
    }
}
