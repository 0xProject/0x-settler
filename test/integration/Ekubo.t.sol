// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {IERC4626} from "@forge-std/interfaces/IERC4626.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";

import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {MainnetSettlerMetaTxn as SettlerMetaTxn} from "src/chains/Mainnet/MetaTxn.sol";
import {Settler} from "src/Settler.sol";
import {SettlerBase} from "src/SettlerBase.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";

import {CORE} from "src/core/Ekubo.sol";
import {NotesLib} from "src/core/FlashAccountingCommon.sol";
import {UnsafeMath} from "src/utils/UnsafeMath.sol";

import {SettlerMetaTxnPairTest} from "./SettlerMetaTxnPairTest.t.sol";
import {AllowanceHolderPairTest} from "./AllowanceHolderPairTest.t.sol";

abstract contract EkuboTest is SettlerMetaTxnPairTest {
    using UnsafeMath for uint256;

    function ekuboPerfectHash() internal view virtual returns (uint256 hashMod, uint256 hashMul) {
        for (hashMod = NotesLib.MAX_TOKENS + 1;; hashMod = hashMod.unsafeInc()) {
            for (hashMul = hashMod >> 1; hashMul < hashMod + (hashMod >> 1); hashMul = hashMul.unsafeInc()) {
                if (
                    mulmod(uint160(address(fromToken())), hashMul, hashMod) % NotesLib.MAX_TOKENS
                        != mulmod(uint160(address(toToken())), hashMul, hashMod) % NotesLib.MAX_TOKENS
                ) {
                    return (hashMul, hashMod);
                }
            }
        }
    }

    function ekuboPoolConfig() internal view virtual returns (bytes32) {
        return bytes32(0);
    }

    function ekuboBlockNumber() internal view virtual returns (uint256) {
        return 22239136;
    }

    modifier setEkuboBlock() {
        uint256 blockNumber = vm.getBlockNumber();
        vm.rollFork(ekuboBlockNumber());
        _;
        vm.rollFork(blockNumber);
    }

    function _setEkuboLabels() private setEkuboBlock {
        vm.label(address(CORE), "Ekubo CORE");
    }

    function ekuboFills() internal view virtual returns (bytes memory) {
        return abi.encodePacked(
            uint16(10_000),
            bytes1(0x01),
            address(toToken()),
            ekuboPoolConfig(),
            uint256(0));
    }

    function ekuboExtraActions(bytes[] memory actions) internal view virtual returns (bytes[] memory) {
        return actions;
    }

    function setUp() public virtual override {
        super.setUp();
        if (ekuboPoolConfig() != bytes32(0)) {
            vm.makePersistent(address(PERMIT2));
            vm.makePersistent(address(allowanceHolder));
            vm.makePersistent(address(settler));
            vm.makePersistent(address(fromToken()));
            vm.makePersistent(address(toToken()));
            _setEkuboLabels();
        }
    }

    function recipient() internal view virtual returns (address) {
        return FROM;
    }

    function metaTxnRecipient() internal view virtual returns (address) {
        return FROM;
    }

    function testEkubo() public skipIf(ekuboPoolConfig() == bytes32(0)) setEkuboBlock {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();

        (uint256 hashMul, uint256 hashMod) = EkuboTest.ekuboPerfectHash();
        bytes[] memory actions = ekuboExtraActions(ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(
                ISettlerActions.EKUBO, (recipient(), address(fromToken()), 10_000, false, hashMul, hashMod, ekuboFills(), 0)
            )
        ));
        
        SettlerBase.AllowedSlippage memory allowedSlippage =
            SettlerBase.AllowedSlippage({recipient: address(0), buyToken: IERC20(address(0)), minAmountOut: 0});
        Settler _settler = settler;
        uint256 beforeBalanceFrom = balanceOf(fromToken(), FROM);
        uint256 beforeBalanceTo = balanceOf(toToken(), FROM);

        vm.startPrank(FROM, FROM);
        snapStartName("settler_ekubo");
        _settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + amount(), beforeBalanceFrom);
    }

    function testEkuboVIP() public skipIf(ekuboPoolConfig() == bytes32(0)) setEkuboBlock {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();

        (uint256 hashMul, uint256 hashMod) = EkuboTest.ekuboPerfectHash();
        bytes[] memory actions = ekuboExtraActions(ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.EKUBO_VIP, (recipient(), false, hashMul, hashMod, ekuboFills(), permit, sig, 0))
        ));
        SettlerBase.AllowedSlippage memory allowedSlippage =
            SettlerBase.AllowedSlippage({recipient: address(0), buyToken: IERC20(address(0)), minAmountOut: 0});
        Settler _settler = settler;
        uint256 beforeBalanceFrom = balanceOf(fromToken(), FROM);
        uint256 beforeBalanceTo = balanceOf(toToken(), FROM);

        vm.startPrank(FROM, FROM);
        snapStartName("settler_ekuboVIP");
        _settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + amount(), beforeBalanceFrom);
    }

    function testEkuboVIPAllowanceHolder() public skipIf(ekuboPoolConfig() == bytes32(0)) setEkuboBlock {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), 0 /* nonce */ );
        bytes memory sig = new bytes(0);

        (uint256 hashMul, uint256 hashMod) = EkuboTest.ekuboPerfectHash();
        bytes[] memory actions = ekuboExtraActions(ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.EKUBO_VIP, (recipient(), false, hashMul, hashMod, ekuboFills(), permit, sig, 0))
        ));
        SettlerBase.AllowedSlippage memory allowedSlippage =
            SettlerBase.AllowedSlippage({recipient: address(0), buyToken: IERC20(address(0)), minAmountOut: 0});
        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        IERC20 _fromToken = fromToken();
        uint256 _amount = amount();
        bytes memory ahData = abi.encodeCall(_settler.execute, (allowedSlippage, actions, bytes32(0)));

        uint256 beforeBalanceFrom = balanceOf(fromToken(), FROM);
        uint256 beforeBalanceTo = balanceOf(toToken(), FROM);

        vm.startPrank(FROM, FROM);
        snapStartName("allowanceHolder_ekuboVIP");
        _allowanceHolder.exec(address(_settler), address(_fromToken), _amount, payable(address(_settler)), ahData);
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + amount(), beforeBalanceFrom);
    }

    function testEkuboMetaTxn() public skipIf(ekuboPoolConfig() == bytes32(0)) setEkuboBlock {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), PERMIT2_FROM_NONCE);

        (uint256 hashMul, uint256 hashMod) = EkuboTest.ekuboPerfectHash();
        bytes[] memory actions = ekuboExtraActions(ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.METATXN_EKUBO_VIP, (metaTxnRecipient(), false, hashMul, hashMod, ekuboFills(), permit, 0))
        ));
        SettlerBase.AllowedSlippage memory allowedSlippage =
            SettlerBase.AllowedSlippage({recipient: address(0), buyToken: IERC20(address(0)), minAmountOut: 0 ether});

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
        uint256 beforeBalanceFrom = balanceOf(fromToken(), FROM);
        uint256 beforeBalanceTo = balanceOf(toToken(), FROM);

        vm.startPrank(address(this), address(this));
        snapStartName("settler_metaTxn_ekubo");
        _settlerMetaTxn.executeMetaTxn(allowedSlippage, actions, bytes32(0), FROM, sig);
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + amount(), beforeBalanceFrom);
    }
}
