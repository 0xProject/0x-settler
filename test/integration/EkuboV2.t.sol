// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {IERC4626} from "@forge-std/interfaces/IERC4626.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";

import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {Settler} from "src/Settler.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";

import {CORE} from "src/core/EkuboV2.sol";
import {NotesLib} from "src/core/FlashAccountingCommon.sol";
import {UnsafeMath} from "src/utils/UnsafeMath.sol";

import {SettlerMetaTxnPairTest} from "./SettlerMetaTxnPairTest.t.sol";

abstract contract EkuboV2Test is SettlerMetaTxnPairTest {
    using UnsafeMath for uint256;

    function ekuboV2Tokens() internal view virtual returns (IERC20, IERC20) {
        return (fromToken(), toToken());
    }

    function ekuboV2PerfectHash() internal view returns (uint256 hashMod, uint256 hashMul) {
        (IERC20 fromToken, IERC20 toToken) = ekuboV2Tokens();
        for (hashMod = NotesLib.MAX_TOKENS + 1;; hashMod = hashMod.unsafeInc()) {
            for (hashMul = hashMod >> 1; hashMul < hashMod + (hashMod >> 1); hashMul = hashMul.unsafeInc()) {
                if (
                    mulmod(uint160(address(fromToken)), hashMul, hashMod) % NotesLib.MAX_TOKENS
                        != mulmod(uint160(address(toToken)), hashMul, hashMod) % NotesLib.MAX_TOKENS
                ) {
                    return (hashMul, hashMod);
                }
            }
        }
    }

    function ekuboV2PoolConfig() internal view virtual returns (bytes32) {
        return bytes32(0);
    }

    function ekuboV2ExtensionConfig() internal view virtual returns (bytes32) {
        return bytes32(0);
    }

    function ekuboV2BlockNumber() internal view virtual returns (uint256) {
        return 22239136;
    }

    modifier setEkuboV2Block() {
        uint256 blockNumber = vm.getBlockNumber();
        vm.rollFork(ekuboV2BlockNumber());
        vm.setEvmVersion("cancun");
        _;
        vm.rollFork(blockNumber);
        vm.setEvmVersion("cancun");
    }

    function _setEkuboV2Labels() private setEkuboV2Block {
        vm.label(address(CORE), "Ekubo CORE");
    }

    function ekuboV2SqrtRatio(IERC20 sellToken, IERC20 buyToken) internal view returns (uint96) {
        bool zeroForOne = (sellToken == IERC20(ETH)) || ((buyToken != IERC20(ETH)) && (sellToken < buyToken));
        return zeroForOne ? 4611797791050542631 : 79227682466138141934206691491;
    }

    function ekuboV2Fills() internal view returns (bytes memory) {
        (IERC20 fromToken, IERC20 toToken) = ekuboV2Tokens();
        return abi.encodePacked(
            uint16(10_000), ekuboV2SqrtRatio(fromToken, toToken), bytes1(0x01), address(toToken), ekuboV2PoolConfig()
        );
    }

    function ekuboV2ExtensionFills() internal view returns (bytes memory) {
        (IERC20 fromToken, IERC20 toToken) = ekuboV2Tokens();
        return abi.encodePacked(
            uint16(42768),
            ekuboV2SqrtRatio(fromToken, toToken),
            bytes1(0x01),
            address(toToken),
            ekuboV2ExtensionConfig()
        );
    }

    function ekuboV2ExtraActions(bytes[] memory actions) internal view virtual returns (bytes[] memory) {
        return actions;
    }

    function setUp() public virtual override {
        super.setUp();
        if (ekuboV2PoolConfig() | ekuboV2ExtensionConfig() != bytes32(0)) {
            vm.makePersistent(address(PERMIT2));
            vm.makePersistent(address(allowanceHolder));
            vm.makePersistent(address(settler));
            vm.makePersistent(address(fromToken()));
            vm.makePersistent(address(toToken()));
            vm.makePersistent(address(FROM));
            vm.etch(FROM, bytes(""));
            _setEkuboV2Labels();
        }
    }

    function ekuboV2Recipient() internal view virtual returns (address) {
        return FROM;
    }

    function testEkuboV2() public skipIf(ekuboV2PoolConfig() == bytes32(0)) setEkuboV2Block {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();

        (uint256 hashMul, uint256 hashMod) = ekuboV2PerfectHash();
        bytes[] memory actions = ekuboV2ExtraActions(
            ActionDataBuilder.build(
                abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
                abi.encodeCall(
                    ISettlerActions.EKUBO,
                    (ekuboV2Recipient(), address(fromToken()), 10_000, false, hashMul, hashMod, ekuboV2Fills(), 0)
                )
            )
        );

        ISettlerBase.AllowedSlippage memory allowedSlippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
        });
        Settler _settler = settler;
        uint256 beforeBalanceFrom = balanceOf(fromToken(), FROM);
        uint256 beforeBalanceTo = balanceOf(toToken(), FROM);

        vm.startPrank(FROM, FROM);
        snapStartName("settler_ekuboV2");
        _settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + amount(), beforeBalanceFrom);
    }

    function testEkuboV2Extension() public skipIf(ekuboV2ExtensionConfig() == bytes32(0)) setEkuboV2Block {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();

        (uint256 hashMul, uint256 hashMod) = ekuboV2PerfectHash();
        bytes[] memory actions = ekuboV2ExtraActions(
            ActionDataBuilder.build(
                abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
                abi.encodeCall(
                    ISettlerActions.EKUBO,
                    (
                        ekuboV2Recipient(),
                        address(fromToken()),
                        10_000,
                        false,
                        hashMul,
                        hashMod,
                        ekuboV2ExtensionFills(),
                        0
                    )
                )
            )
        );

        ISettlerBase.AllowedSlippage memory allowedSlippage = ISettlerBase.AllowedSlippage({
            recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0
        });
        Settler _settler = settler;
        uint256 beforeBalanceFrom = balanceOf(fromToken(), FROM);
        uint256 beforeBalanceTo = balanceOf(toToken(), FROM);

        vm.startPrank(FROM, FROM);
        snapStartName("settler_ekuboV2Extension");
        _settler.execute(allowedSlippage, actions, bytes32(0));
        snapEnd();
        vm.stopPrank();

        uint256 afterBalanceTo = toToken().balanceOf(FROM);
        assertGt(afterBalanceTo, beforeBalanceTo);
        uint256 afterBalanceFrom = fromToken().balanceOf(FROM);
        assertEq(afterBalanceFrom + amount(), beforeBalanceFrom);
    }
}
