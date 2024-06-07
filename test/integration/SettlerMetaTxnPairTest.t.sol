// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "src/IERC20.sol";
import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";

import {SettlerBasePairTest, Shim} from "./SettlerBasePairTest.t.sol";
import {ICurveV2Pool} from "./vendor/ICurveV2Pool.sol";
import {IZeroEx} from "./vendor/IZeroEx.sol";

import {LibBytes} from "../utils/LibBytes.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";

import {SafeTransferLib} from "src/vendor/SafeTransferLib.sol";
import {AddressDerivation} from "src/utils/AddressDerivation.sol";

import {AllowanceHolder} from "src/allowanceholder/AllowanceHolder.sol";
import {MainnetSettlerMetaTxn as SettlerMetaTxn} from "src/chains/Mainnet.sol";
import {Settler} from "src/Settler.sol";
import {SettlerBase} from "src/SettlerBase.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {RfqOrderSettlement} from "src/core/RfqOrderSettlement.sol";

contract ERC6492Signer {
    address internal immutable actualSigner;

    constructor(address _actualSigner) {
        actualSigner = _actualSigner;
    }

    function isValidSignature(bytes32 hash, bytes memory sig) external view returns (bytes4) {
        assert(sig.length == 65);
        uint8 v;
        bytes32 r;
        bytes32 s;
        assembly ("memory-safe") {
            v := mload(add(0x41, sig))
            r := mload(add(0x20, sig))
            s := mload(add(0x40, sig))
        }
        require(ecrecover(hash, v, r, s) == actualSigner);
        return this.isValidSignature.selector;
    }
}

contract ERC6492Factory {
    function deploy(bytes32 salt, address actualSigner) external {
        new ERC6492Signer{salt: salt}(actualSigner);
    }
}

abstract contract SettlerMetaTxnPairTest is SettlerBasePairTest {
    using SafeTransferLib for IERC20;
    using LibBytes for bytes;

    SettlerMetaTxn internal settlerMetaTxn;
    ERC6492Factory internal erc6492Factory;

    function setUp() public virtual override {
        super.setUp();

        uint256 forkChainId = (new Shim()).chainId();
        vm.chainId(31337);
        settlerMetaTxn = new SettlerMetaTxn(bytes20(0));
        vm.chainId(forkChainId);

        // ### Taker ###
        safeApproveIfBelow(fromToken(), FROM, address(PERMIT2), amount());

        // ### Maker / Seller ###
        // Rfq inside of Settler
        safeApproveIfBelow(toToken(), MAKER, address(PERMIT2), amount());

        warmPermit2Nonce(FROM);
        warmPermit2Nonce(MAKER);

        erc6492Factory = new ERC6492Factory();
        address erc6492Signer = AddressDerivation.deriveDeterministicContract(
            address(erc6492Factory),
            bytes32(uint256(1)),
            keccak256(bytes.concat(type(ERC6492Signer).creationCode, abi.encode(FROM)))
        );
        deal(address(fromToken()), erc6492Signer, amount());
        safeApproveIfBelow(fromToken(), erc6492Signer, address(PERMIT2), amount());
        warmPermit2Nonce(erc6492Signer);
    }

    function uniswapV3Path() internal virtual returns (bytes memory);

    /// @dev Performs an direct RFQ trade between MAKER and FROM
    // Funds are transferred MAKER->FROM and FROM->MAKER
    function testSettler_rfq() public {
        ISignatureTransfer.PermitTransferFrom memory makerPermit =
            defaultERC20PermitTransfer(address(toToken()), amount(), PERMIT2_MAKER_NONCE);
        ISignatureTransfer.PermitTransferFrom memory takerPermit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), PERMIT2_FROM_NONCE);

        RfqOrderSettlement.Consideration memory makerConsideration = RfqOrderSettlement.Consideration({
            token: address(fromToken()),
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
            abi.encodeCall(ISettlerActions.RFQ_VIP, (FROM, makerPermit, MAKER, makerSig, takerPermit, takerSig))
        );

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_rfq");
        _settler.execute(
            SettlerBase.AllowedSlippage({recipient: address(0), buyToken: IERC20(address(0)), minAmountOut: 0 ether}),
            actions
        );
        snapEnd();
    }

    bytes32 private constant FULL_PERMIT2_WITNESS_TYPEHASH = keccak256(
        "PermitWitnessTransferFrom(TokenPermissions permitted,address spender,uint256 nonce,uint256 deadline,SlippageAndActions slippageAndActions)SlippageAndActions(address recipient,address buyToken,uint256 minAmountOut,bytes[] actions)TokenPermissions(address token,uint256 amount)"
    );
    bytes32 private constant SLIPPAGE_AND_ACTIONS_TYPEHASH =
        keccak256("SlippageAndActions(address recipient,address buyToken,uint256 minAmountOut,bytes[] actions)");

    function testSettler_metaTxn_uniswapV3() public {
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
            SettlerBase.AllowedSlippage({recipient: address(0), buyToken: IERC20(address(0)), minAmountOut: 0 ether}),
            actions,
            FROM,
            sig
        );
        snapEnd();
    }

    function testSettler_metaTxn_uniswapV3VIP() public {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), PERMIT2_FROM_NONCE);

        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.METATXN_UNISWAPV3_VIP, (FROM, uniswapV3Path(), permit, 0))
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
            SettlerBase.AllowedSlippage({recipient: address(0), buyToken: IERC20(address(0)), minAmountOut: 0 ether}),
            actions,
            FROM,
            sig
        );
        snapEnd();
    }

    function testSettler_metaTxn_rfq() public {
        ISignatureTransfer.PermitTransferFrom memory makerPermit =
            defaultERC20PermitTransfer(address(toToken()), amount(), PERMIT2_MAKER_NONCE);
        ISignatureTransfer.PermitTransferFrom memory takerPermit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), PERMIT2_FROM_NONCE);

        RfqOrderSettlement.Consideration memory makerConsideration = RfqOrderSettlement.Consideration({
            token: address(fromToken()),
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
            abi.encodeCall(ISettlerActions.METATXN_RFQ_VIP, (FROM, makerPermit, MAKER, makerSig, takerPermit))
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
            SettlerBase.AllowedSlippage({recipient: address(0), buyToken: IERC20(address(0)), minAmountOut: 0 ether}),
            actions,
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
            token: address(fromToken()),
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
            SettlerBase.AllowedSlippage({recipient: FROM, buyToken: toToken(), minAmountOut: amount() * 9_000 / 10_000}),
            actions
        );
        snapEnd();
    }

    function testSettler_erc6492() public {
        bytes32 salt = bytes32(uint256(1));
        address erc6492Signer = AddressDerivation.deriveDeterministicContract(
            address(erc6492Factory), salt, keccak256(bytes.concat(type(ERC6492Signer).creationCode, abi.encode(FROM)))
        );

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
        bytes32 witness = keccak256(abi.encode(SLIPPAGE_AND_ACTIONS_TYPEHASH, FROM, fromToken(), amount(), actionsHash));
        bytes memory sig = getPermitWitnessTransferSignature(
            permit, address(settlerMetaTxn), FROM_PRIVATE_KEY, FULL_PERMIT2_WITNESS_TYPEHASH, witness, permit2Domain
        );
        sig = bytes.concat(
            abi.encode(address(erc6492Factory), abi.encodeCall(erc6492Factory.deploy, (salt, FROM)), sig),
            bytes32(0x6492649264926492649264926492649264926492649264926492649264926492)
        );

        SettlerMetaTxn _settlerMetaTxn = settlerMetaTxn;
        vm.startPrank(address(this), address(this));
        snapStartName("settler_metaTxn_erc6492");
        _settlerMetaTxn.executeMetaTxn(
            SettlerBase.AllowedSlippage({recipient: FROM, buyToken: fromToken(), minAmountOut: amount()}),
            actions,
            erc6492Signer,
            sig
        );
        snapEnd();
    }
}
