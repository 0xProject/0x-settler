// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {IERC4626} from "@forge-std/interfaces/IERC4626.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";

import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {Settler} from "src/Settler.sol";
import {SettlerMetaTxn} from "src/SettlerMetaTxn.sol";
import {SettlerBase} from "src/SettlerBase.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";
import {BnbSettler} from "src/chains/Bnb/TakerSubmitted.sol";
import {BnbSettlerMetaTxn} from "src/chains/Bnb/MetaTxn.sol";

import {NotesLib} from "src/core/FlashAccountingCommon.sol";
import {UnsafeMath} from "src/utils/UnsafeMath.sol";

import {SettlerMetaTxnPairTest} from "./SettlerMetaTxnPairTest.t.sol";
import {AllowanceHolderPairTest} from "./AllowanceHolderPairTest.t.sol";
import {
    PancakeInfinity,
    PoolKey,
    VAULT,
    CL_MANAGER,
    BIN_MANAGER,
    PoolId,
    IPancakeInfinityPoolManager
} from "src/core/PancakeInfinity.sol";

// Tokens Currently in Pools
// CAKE  0x0e09fabb73bd3ade0a17ecc321fd13a19e81ce82
// USDT  0x55d398326f99059ff775485246999027b3197955
// BTCB  0x7130d2a12b9bcbfae4f2634d864a1ee1ce3ead9c
// WBNB  0xbb4cdb9cbd36b01bd1cbaebf2de08d9173bc095c
// mCake 0x581fa684d0ec11ccb46b1d92f1f24c8a3f95c0ca
// BNB   0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee (0x0 for the Protocol)

// IDs (IN BIN)
// USDT <> CAKE 0xd421a3cddb87ef1209ad84ab77fafdd53c0d7d7f5c6456bd7fef86beac302f73
// BNB  <> USDT 0xe5b2c5fa2851575d3d8963b41cd2b798f3647ef3d24b748bbcc2c216045c3139
// BNB  <> CAKE 0x7e98a7b02ae97697b5c66f2b605351ef7853dea26ba5a737d701bdb6bd918e99

// IDS (IN CL)
// BNB  <> BTCB 0xf7c6dfc8e278c946971b92491f635068e3389d6f87ef030340b99d7d2cd8944b
// BNB  <> CAKE 0xb4ae729f31646d957b3de404ecd42d1fb65d679a97ae12d39106370d07e85371
// USDT <> CAKE 0xe20065b2081f13ac8501ee5ae19eeecd9678a25343f0e6d4d2ba288b7e013793
// USDT <> BNB  0x6ea8176562c04242188f469e4da27983876b3091033e010159a8ac582c26f99c
// CAKE <> WBNB 0x4128d60036a6c41de89d19cacb70b04ad3345e6f142412e20616bcb49c8d730c

// Initialize(bytes32,address,address,address,uint24,bytes32,uint160,int24)

abstract contract PancakeInfinityTest is SettlerMetaTxnPairTest {
    using UnsafeMath for uint256;

    function testBlockNumber() internal pure virtual override returns (uint256) {
        return 48420182;
    }

    function testChainId() internal pure virtual override returns (string memory) {
        return "bnb";
    }

    function pancakeInfinityPerfectHash() internal view virtual returns (uint256 hashMod, uint256 hashMul) {
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

    function _setPancakeInfinityLabels() private {
        vm.label(address(VAULT), "Vault");
        vm.label(address(CL_MANAGER), "CLPoolManager");
        vm.label(address(BIN_MANAGER), "BINPoolManager");
    }

    function pancakeInfinityFills() internal view virtual returns (bytes memory) {
        bytes32 poolId_ = poolId();
        uint8 managerId = poolManagerId();
        PoolKey memory poolKey = (
            managerId == 0 ? IPancakeInfinityPoolManager(CL_MANAGER) : IPancakeInfinityPoolManager(BIN_MANAGER)
        ).poolIdToPoolKey(PoolId.wrap(poolId_));

        return abi.encodePacked(
            uint16(10_000),
            bytes1(0x01),
            address(toToken()),
            poolKey.hooks,
            managerId,
            poolKey.fee,
            poolKey.parameters,
            uint24(0),
            bytes("")
        );
    }

    function poolId() internal view virtual returns (bytes32) {
        return bytes32(0x0000000000000000000000000000000000000000000000000000000000000000);
    }

    function poolManagerId() internal view virtual returns (uint8) {
        return 0;
    }

    function setUp() public virtual override {
        super.setUp();
        // vm.makePersistent(address(PERMIT2));
        // vm.makePersistent(address(allowanceHolder));
        // vm.makePersistent(address(settler));
        // vm.makePersistent(address(fromToken()));
        // vm.makePersistent(address(toToken()));
        _setPancakeInfinityLabels();
    }

    function testPancakeInfinity() public skipIf(poolId() == bytes32(0x0)) {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();

        (uint256 hashMul, uint256 hashMod) = pancakeInfinityPerfectHash();
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(
                ISettlerActions.PANCAKE_INFINITY,
                (FROM, address(fromToken()), 10_000, false, hashMul, hashMod, pancakeInfinityFills(), 0)
            )
        );

        SettlerBase.AllowedSlippage memory allowedSlippage =
            SettlerBase.AllowedSlippage({recipient: address(0), buyToken: IERC20(address(0)), minAmountOut: 0});
        Settler _settler = settler;
        uint256 beforeBalanceFrom = balanceOf(fromToken(), FROM);
        uint256 beforeBalanceTo = balanceOf(toToken(), FROM);

        vm.startPrank(FROM, FROM);
        snapStartName("settler_pancakeInfinity");
        _settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + amount(), beforeBalanceFrom);
    }

    function testPancakeInfinityVIP() public skipIf(poolId() == bytes32(0x0)) {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();

        (uint256 hashMul, uint256 hashMod) = pancakeInfinityPerfectHash();
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.PANCAKE_INFINITY_VIP,
                (FROM, false, hashMul, hashMod, pancakeInfinityFills(), permit, sig, 0)
            )
        );
        SettlerBase.AllowedSlippage memory allowedSlippage =
            SettlerBase.AllowedSlippage({recipient: address(0), buyToken: IERC20(address(0)), minAmountOut: 0});
        Settler _settler = settler;
        uint256 beforeBalanceFrom = balanceOf(fromToken(), FROM);
        uint256 beforeBalanceTo = balanceOf(toToken(), FROM);

        vm.startPrank(FROM, FROM);
        snapStartName("settler_pancakeInfinityVIP");
        _settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + amount(), beforeBalanceFrom);
    }

    function testPancakeInfinityVIPAllowanceHolder() public skipIf(poolId() == bytes32(0x0)) {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), 0 /* nonce */ );
        bytes memory sig = new bytes(0);

        (uint256 hashMul, uint256 hashMod) = pancakeInfinityPerfectHash();
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.PANCAKE_INFINITY_VIP,
                (FROM, false, hashMul, hashMod, pancakeInfinityFills(), permit, sig, 0)
            )
        );
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
        snapStartName("allowanceHolder_pancakeInfinityVIP");
        _allowanceHolder.exec(address(_settler), address(_fromToken), _amount, payable(address(_settler)), ahData);
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + amount(), beforeBalanceFrom);
    }

    function testPancakeInfinityMetaTxn() public skipIf(poolId() == bytes32(0x0)) {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), PERMIT2_FROM_NONCE);

        (uint256 hashMul, uint256 hashMod) = pancakeInfinityPerfectHash();
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.METATXN_PANCAKE_INFINITY_VIP,
                (FROM, false, hashMul, hashMod, pancakeInfinityFills(), permit, 0)
            )
        );
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
        snapStartName("settler_metaTxn_pancakeInfinity");
        _settlerMetaTxn.executeMetaTxn(allowedSlippage, actions, bytes32(0), FROM, sig);
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + amount(), beforeBalanceFrom);
    }
}

contract USDTCAKETest is PancakeInfinityTest {
    function settlerInitCode() internal virtual override returns (bytes memory) {
        return bytes.concat(type(BnbSettler).creationCode, abi.encode(bytes20(0)));
    }

    function settlerMetaTxnInitCode() internal virtual override returns (bytes memory) {
        return bytes.concat(type(BnbSettlerMetaTxn).creationCode, abi.encode(bytes20(0)));
    }

    function testName() internal pure override returns (string memory) {
        return "USDT-CAKE";
    }

    function fromToken() internal pure override returns (IERC20) {
        return IERC20(0x55d398326f99059fF775485246999027B3197955); // USDT
    }

    function toToken() internal pure override returns (IERC20) {
        return IERC20(0x0E09FaBB73Bd3Ade0a17ECC321fD13a19e81cE82); // CAKE
    }

    function poolId() internal view virtual override returns (bytes32) {
        return bytes32(0xe20065b2081f13ac8501ee5ae19eeecd9678a25343f0e6d4d2ba288b7e013793);
    }

    function amount() internal view virtual override returns (uint256) {
        return 1 ether;
    }

    function uniswapV3Path() internal view virtual override returns (bytes memory) {
        return bytes("");
    }
}
