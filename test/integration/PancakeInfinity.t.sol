// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {IERC4626} from "@forge-std/interfaces/IERC4626.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";

import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {Settler} from "src/Settler.sol";
import {SettlerMetaTxn} from "src/SettlerMetaTxn.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";
import {BnbSettler} from "src/chains/Bnb/TakerSubmitted.sol";
import {BnbSettlerMetaTxn} from "src/chains/Bnb/MetaTxn.sol";

import {NotesLib} from "src/core/FlashAccountingCommon.sol";
import {UnsafeMath} from "src/utils/UnsafeMath.sol";
import {tmp} from "src/utils/512Math.sol";

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

interface IPancakeInfinityCLPoolManagerSlot0 {
    function getSlot0(bytes32 poolId) external view returns (uint160 sqrtPriceX96);
}

abstract contract PancakeInfinityTest is AllowanceHolderPairTest, SettlerMetaTxnPairTest {
    using UnsafeMath for uint256;

    uint160 private constant MIN_SQRT_RATIO = 4295128740;
    uint160 private constant MAX_SQRT_RATIO = 1461446703485210103287273052203988822378723970341;
    uint256 private constant Q96 = 1 << 96;
    uint256 private constant SQRT_2_Q96 = 112045541949572279837463876454;

    function uniswapV3Path()
        internal
        view
        virtual
        override(AllowanceHolderPairTest, SettlerMetaTxnPairTest)
        returns (bytes memory)
    {
        return bytes("");
    }

    function uniswapV2Pool() internal view virtual override returns (address) {
        return address(0);
    }

    function _testBlockNumber() internal pure virtual override returns (uint256) {
        return 48420182;
    }

    function _testChainId() internal pure virtual override returns (string memory) {
        return "bnb";
    }

    function settlerInitCode() internal virtual override returns (bytes memory) {
        return bytes.concat(type(BnbSettler).creationCode, abi.encode(bytes20(0)));
    }

    function settlerMetaTxnInitCode() internal virtual override returns (bytes memory) {
        return bytes.concat(type(BnbSettlerMetaTxn).creationCode, abi.encode(bytes20(0)));
    }

    function extraActions(bytes[] memory actions) internal view virtual returns (bytes[] memory) {
        return actions;
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

    function _readSlot0Cold(bytes32 poolId_) private view returns (uint160 sqrtPriceX96) {
        // Revert with the return value so the access list stays cold for gas snapshots.
        (bool ok, bytes memory data) =
            address(this).staticcall(abi.encodeCall(this._readSlot0AndRevert, (poolId_)));
        if (ok || data.length != 32) {
            revert();
        }
        return abi.decode(data, (uint160));
    }

    function _readSlot0AndRevert(bytes32 poolId_) external view {
        uint160 sqrtPriceX96 = IPancakeInfinityCLPoolManagerSlot0(address(CL_MANAGER)).getSlot0(poolId_);
        assembly ("memory-safe") {
            mstore(0x00, sqrtPriceX96)
            revert(0x00, 0x20)
        }
    }

    function sqrtPriceLimitX96(IERC20 sellToken, IERC20 buyToken)
        internal
        view
        virtual
        override
        returns (uint160)
    {
        if (poolManagerId() != 0 || poolId() == bytes32(0)) {
            return super.sqrtPriceLimitX96(sellToken, buyToken);
        }

        uint160 current = _readSlot0Cold(poolId());
        bool zeroForOne = (sellToken == IERC20(ETH)) || ((buyToken != IERC20(ETH)) && (sellToken < buyToken));

        uint256 limitX96;
        if (zeroForOne) {
            limitX96 = tmp().omul(uint256(current), Q96).div(SQRT_2_Q96);
            if (limitX96 < MIN_SQRT_RATIO) {
                limitX96 = MIN_SQRT_RATIO;
            }
        } else {
            limitX96 = tmp().omul(uint256(current), SQRT_2_Q96).div(Q96);
            if (limitX96 > MAX_SQRT_RATIO) {
                limitX96 = MAX_SQRT_RATIO;
            }
        }
        return uint160(limitX96);
    }

    function pancakeInfinityFills(IERC20 fromToken, IERC20 toToken) internal view virtual returns (bytes memory) {
        bytes32 poolId_ = poolId();
        uint8 managerId = poolManagerId();
        PoolKey memory poolKey = (
            managerId == 0 ? IPancakeInfinityPoolManager(CL_MANAGER) : IPancakeInfinityPoolManager(BIN_MANAGER)
        ).poolIdToPoolKey(PoolId.wrap(poolId_));

        return abi.encodePacked(
            uint16(10_000),
            sqrtPriceLimitX96(fromToken, toToken),
            bytes1(0x01),
            toToken,
            poolKey.hooks,
            managerId,
            poolKey.fee,
            poolKey.parameters,
            uint24(0),
            bytes("")
        );
    }

    function pancakeInfinityFills() internal view virtual returns (bytes memory) {
        return pancakeInfinityFills(fromToken(), toToken());
    }

    function poolId() internal view virtual returns (bytes32) {
        return bytes32(0);
    }

    function poolManagerId() internal view virtual returns (uint8) {
        return 0;
    }

    function recipient() internal view virtual returns (address) {
        return FROM;
    }

    function metaTxnRecipient() internal view virtual returns (address) {
        return FROM;
    }

    function setUp() public virtual override(AllowanceHolderPairTest, SettlerMetaTxnPairTest) {
        // for some reason, the RPC hangs if we don't have this
        vm.makePersistent(address(PERMIT2));
        vm.makePersistent(address(allowanceHolder));
        vm.makePersistent(address(settler));
        vm.makePersistent(address(fromToken()));
        vm.makePersistent(address(toToken()));

        super.setUp();
        _setPancakeInfinityLabels();
    }

    function testPancakeInfinity() public skipIf(poolId() == bytes32(0x0)) {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();

        (uint256 hashMul, uint256 hashMod) = pancakeInfinityPerfectHash();
        bytes[] memory actions = extraActions(
            ActionDataBuilder.build(
                abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
                abi.encodeCall(
                    ISettlerActions.PANCAKE_INFINITY,
                    (recipient(), address(fromToken()), 10_000, false, hashMul, hashMod, pancakeInfinityFills(), 0)
                )
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
        bytes[] memory actions = extraActions(
            ActionDataBuilder.build(
                abi.encodeCall(
                    ISettlerActions.PANCAKE_INFINITY_VIP,
                    (recipient(), permit, false, hashMul, hashMod, pancakeInfinityFills(), sig, 0)
                )
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
        snapStartName("settler_pancakeInfinityVIP");
        _settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        // The pool has comparatively little liquidity, so the order cannot be
        // fully filled. We just check that it at least partially filled.
        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertLt(afterBalanceFrom, beforeBalanceFrom);
    }

    function testPancakeInfinityVIPAllowanceHolder() public skipIf(poolId() == bytes32(0x0)) {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), 0 /* nonce */ );
        bytes memory sig = new bytes(0);

        (uint256 hashMul, uint256 hashMod) = pancakeInfinityPerfectHash();
        bytes[] memory actions = extraActions(
            ActionDataBuilder.build(
                abi.encodeCall(
                    ISettlerActions.PANCAKE_INFINITY_VIP,
                    (recipient(), permit, false, hashMul, hashMod, pancakeInfinityFills(), sig, 0)
                )
            )
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
        snapStartName("allowanceHolder_pancakeInfinityVIP");
        _allowanceHolder.exec(address(_settler), address(_fromToken), _amount, payable(address(_settler)), ahData);
        snapEnd();
        vm.stopPrank();

        // The pool has comparatively little liquidity, so the order cannot be
        // fully filled. We just check that it at least partially filled.
        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertLt(afterBalanceFrom, beforeBalanceFrom);
    }

    function testPancakeInfinityMetaTxn() public skipIf(poolId() == bytes32(0x0)) {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(fromToken()), amount(), PERMIT2_FROM_NONCE);

        (uint256 hashMul, uint256 hashMod) = pancakeInfinityPerfectHash();
        bytes[] memory actions = extraActions(
            ActionDataBuilder.build(
                abi.encodeCall(
                    ISettlerActions.METATXN_PANCAKE_INFINITY_VIP,
                    (metaTxnRecipient(), permit, false, hashMul, hashMod, pancakeInfinityFills(), 0)
                )
            )
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
        snapStartName("settler_metaTxn_pancakeInfinity");
        _settlerMetaTxn.executeMetaTxn(allowedSlippage, actions, bytes32(0), FROM, sig);
        snapEnd();
        vm.stopPrank();

        // The pool has comparatively little liquidity, so the order cannot be
        // fully filled. We just check that it at least partially filled.
        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertLt(afterBalanceFrom, beforeBalanceFrom);
    }
}

contract USDTCAKETest is PancakeInfinityTest {
    function _testName() internal pure override returns (string memory) {
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
}

contract USDTWBNBTest is PancakeInfinityTest {
    function _testName() internal pure override returns (string memory) {
        return "USDT-WBNB";
    }

    function fromToken() internal pure override returns (IERC20) {
        return IERC20(0x55d398326f99059fF775485246999027B3197955); // USDT
    }

    function toToken() internal pure override returns (IERC20) {
        return IERC20(0xbb4CdB9CBd36B01bD1cBaEBF2De08d9173bc095c); // WBNB
    }

    function poolId() internal view virtual override returns (bytes32) {
        return bytes32(0x160835004763453c4783f82357b8597371ba8c9c10be5ff9f63f56663e0a105f);
    }

    function amount() internal view virtual override returns (uint256) {
        return 1 ether;
    }

    function poolManagerId() internal view virtual override returns (uint8) {
        return 1;
    }

    function recipient() internal view virtual override returns (address) {
        return address(settler);
    }

    function metaTxnRecipient() internal view virtual override returns (address) {
        return address(settlerMetaTxn);
    }

    function extraActions(bytes[] memory actions) internal view virtual override returns (bytes[] memory) {
        bytes[] memory data = new bytes[](actions.length + 2);
        address wbnb = address(toToken());
        address bnb = 0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE;
        for (uint256 i; i < actions.length; i++) {
            data[i] = actions[i];
        }
        data[actions.length] = abi.encodeCall(ISettlerActions.BASIC, (bnb, 10_000, wbnb, 0, ""));
        data[actions.length + 1] = abi.encodeCall(
            ISettlerActions.BASIC, (wbnb, 10_000, wbnb, 36, abi.encodeCall(toToken().transfer, (FROM, uint256(0))))
        );
        return data;
    }

    function pancakeInfinityFills() internal view virtual override returns (bytes memory) {
        return pancakeInfinityFills(fromToken(), ETH);
    }
}
