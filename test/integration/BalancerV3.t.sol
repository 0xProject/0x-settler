// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {IERC4626} from "@forge-std/interfaces/IERC4626.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";

import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {MainnetSettlerMetaTxn as SettlerMetaTxn} from "src/chains/Mainnet/MetaTxn.sol";
import {Settler} from "src/Settler.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";

import {VAULT} from "src/core/BalancerV3.sol";
import {NotesLib} from "src/core/FlashAccountingCommon.sol";
import {UnsafeMath} from "src/utils/UnsafeMath.sol";

import {SettlerMetaTxnPairTest} from "./SettlerMetaTxnPairTest.t.sol";
import {AllowanceHolderPairTest} from "./AllowanceHolderPairTest.t.sol";

abstract contract BalancerV3Test is SettlerMetaTxnPairTest, AllowanceHolderPairTest {
    using UnsafeMath for uint256;

    function balancerV3Pool() internal view virtual returns (address) {
        return address(0);
    }

    function balancerV3BloackNumber() internal view virtual returns (uint256) {
        return 21581659;
    }

    function fromTokenWrapped() internal view virtual returns (IERC4626) {
        return IERC4626(address(0));
    }

    function toTokenWrapped() internal view virtual returns (IERC4626) {
        return IERC4626(address(0));
    }

    function balancerPerfectHash() internal view virtual returns (uint256 hashMod, uint256 hashMul) {
        for (hashMod = NotesLib.MAX_TOKENS + 1;; hashMod = hashMod.unsafeInc()) {
            for (hashMul = hashMod >> 1; hashMul < hashMod + (hashMod >> 1); hashMul = hashMul.unsafeInc()) {
                if (
                    mulmod(uint160(address(fromToken())), hashMul, hashMod) % NotesLib.MAX_TOKENS
                        == mulmod(uint160(address(fromTokenWrapped())), hashMul, hashMod) % NotesLib.MAX_TOKENS
                ) {
                    continue;
                }
                if (
                    mulmod(uint160(address(fromToken())), hashMul, hashMod) % NotesLib.MAX_TOKENS
                        == mulmod(uint160(address(toTokenWrapped())), hashMul, hashMod) % NotesLib.MAX_TOKENS
                ) {
                    continue;
                }
                if (
                    mulmod(uint160(address(fromToken())), hashMul, hashMod) % NotesLib.MAX_TOKENS
                        == mulmod(uint160(address(toToken())), hashMul, hashMod) % NotesLib.MAX_TOKENS
                ) {
                    continue;
                }
                if (
                    mulmod(uint160(address(fromTokenWrapped())), hashMul, hashMod) % NotesLib.MAX_TOKENS
                        == mulmod(uint160(address(toTokenWrapped())), hashMul, hashMod) % NotesLib.MAX_TOKENS
                ) {
                    continue;
                }
                if (
                    mulmod(uint160(address(fromTokenWrapped())), hashMul, hashMod) % NotesLib.MAX_TOKENS
                        == mulmod(uint160(address(toToken())), hashMul, hashMod) % NotesLib.MAX_TOKENS
                ) {
                    continue;
                }
                if (
                    mulmod(uint160(address(toTokenWrapped())), hashMul, hashMod) % NotesLib.MAX_TOKENS
                        == mulmod(uint160(address(toToken())), hashMul, hashMod) % NotesLib.MAX_TOKENS
                ) {
                    continue;
                }
                return (hashMul, hashMod);
            }
        }
    }

    function _setBalancerV3Labels() private setBalancerV3Block {
        vm.label(address(VAULT), "BalancerV3 vault");
        vm.label(balancerV3Pool(), string.concat("BalancerV3 pool: ", fromToken().symbol(), "/", toToken().symbol()));
        vm.label(address(fromTokenWrapped()), fromTokenWrapped().symbol());
        vm.label(address(toTokenWrapped()), toTokenWrapped().symbol());
    }

    function setUp() public virtual override(SettlerMetaTxnPairTest, AllowanceHolderPairTest) {
        super.setUp();
        if (balancerV3Pool() != address(0)) {
            vm.makePersistent(address(PERMIT2));
            vm.makePersistent(address(allowanceHolder));
            vm.makePersistent(address(settler));
            vm.makePersistent(address(settlerMetaTxn));
            vm.makePersistent(address(fromToken()));
            vm.makePersistent(address(toToken()));
            vm.makePersistent(address(fromTokenWrapped()));
            vm.makePersistent(address(toTokenWrapped()));
            _setBalancerV3Labels();
        }
    }

    modifier setBalancerV3Block() {
        uint256 blockNumber = vm.getBlockNumber();
        vm.rollFork(balancerV3BloackNumber());
        vm.setEvmVersion("cancun");
        _;
        vm.rollFork(blockNumber);
        vm.setEvmVersion("cancun");
    }

    function fills() internal virtual returns (bytes memory) {
        return bytes.concat(
            // wrap `fromToken()` to `fromTokenWrapped()`
            bytes2(uint16(2 ** 15 | 10000)),
            bytes1(uint8(1)),
            bytes20(uint160(address(fromTokenWrapped()))),
            // swap `fromTokenWrapped()` to `toTokenWrapped()`
            bytes2(uint16(10000)),
            bytes1(uint8(2)),
            bytes20(uint160(address(toTokenWrapped()))),
            bytes20(uint160(balancerV3Pool())),
            bytes3(uint24(0)),
            // unwrap `toTokenWrapped()` to `toToken()`
            bytes2(uint16(2 ** 14 | 10000)),
            bytes1(uint8(2)),
            bytes20(uint160(address(toToken())))
        );
    }

    function testBalancerV3() public skipIf(balancerV3Pool() == address(0)) setBalancerV3Block {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();

        (uint256 hashMul, uint256 hashMod) = balancerPerfectHash();
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(
                ISettlerActions.BALANCERV3, (FROM, address(fromToken()), 10_000, false, hashMul, hashMod, fills(), 0)
            )
        );
        ISettlerBase.AllowedSlippage memory allowedSlippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(0)),
            buyToken: IERC20(address(0)),
            minAmountOut: 0
        });
        Settler _settler = settler;
        uint256 beforeBalanceFrom = balanceOf(fromToken(), FROM);
        uint256 beforeBalanceTo = balanceOf(toToken(), FROM);

        vm.startPrank(FROM, FROM);
        snapStartName("settler_balancerV3");
        _settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + amount(), beforeBalanceFrom);
    }

    function testBalancerV3VIP() public skipIf(balancerV3Pool() == address(0)) setBalancerV3Block {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();

        (uint256 hashMul, uint256 hashMod) = balancerPerfectHash();
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.BALANCERV3_VIP, (FROM, permit, false, hashMul, hashMod, fills(), sig, 0))
        );
        ISettlerBase.AllowedSlippage memory allowedSlippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(0)),
            buyToken: IERC20(address(0)),
            minAmountOut: 0
        });
        Settler _settler = settler;
        uint256 beforeBalanceFrom = balanceOf(fromToken(), FROM);
        uint256 beforeBalanceTo = balanceOf(toToken(), FROM);

        vm.startPrank(FROM, FROM);
        snapStartName("settler_balancerV3VIP");
        _settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + amount(), beforeBalanceFrom);
    }

    function testBalancerV3VIPAllowanceHolder() public skipIf(balancerV3Pool() == address(0)) setBalancerV3Block {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), 0 /* nonce */ );
        bytes memory sig = new bytes(0);

        (uint256 hashMul, uint256 hashMod) = balancerPerfectHash();
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.BALANCERV3_VIP, (FROM, permit, false, hashMul, hashMod, fills(), sig, 0))
        );
        ISettlerBase.AllowedSlippage memory allowedSlippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(0)),
            buyToken: IERC20(address(0)),
            minAmountOut: 0
        });
        IAllowanceHolder _allowanceHolder = allowanceHolder;
        Settler _settler = settler;
        IERC20 _fromToken = fromToken();
        uint256 _amount = amount();
        bytes memory ahData = abi.encodeCall(_settler.execute, (allowedSlippage, actions, bytes32(0)));

        uint256 beforeBalanceFrom = balanceOf(fromToken(), FROM);
        uint256 beforeBalanceTo = balanceOf(toToken(), FROM);

        vm.startPrank(FROM, FROM);
        snapStartName("allowanceHolder_balancerV3VIP");
        _allowanceHolder.exec(address(_settler), address(_fromToken), _amount, payable(address(_settler)), ahData);
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + amount(), beforeBalanceFrom);
    }

    function testBalancerV3MetaTxn() public skipIf(balancerV3Pool() == address(0)) setBalancerV3Block {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), PERMIT2_FROM_NONCE);

        (uint256 hashMul, uint256 hashMod) = balancerPerfectHash();
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.METATXN_BALANCERV3_VIP, (FROM, permit, false, hashMul, hashMod, fills(), 0))
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
        uint256 beforeBalanceFrom = balanceOf(fromToken(), FROM);
        uint256 beforeBalanceTo = balanceOf(toToken(), FROM);

        vm.startPrank(address(this), address(this));
        snapStartName("settler_metaTxn_balancerV3");
        _settlerMetaTxn.executeMetaTxn(allowedSlippage, actions, bytes32(0), FROM, sig);
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + amount(), beforeBalanceFrom);
    }

    function uniswapV3Path()
        internal
        view
        virtual
        override(SettlerMetaTxnPairTest, AllowanceHolderPairTest)
        returns (bytes memory);
}
