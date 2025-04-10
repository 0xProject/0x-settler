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

import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";

abstract contract EkuboTest is SettlerBasePairTest {
    using UnsafeMath for uint256;

    function perfectHash() internal view virtual returns (uint256 hashMod, uint256 hashMul) {
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

    function testEkubo() public skipIf(ekuboPoolConfig() == bytes32(0)) setEkuboBlock {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();

        (uint256 hashMul, uint256 hashMod) = EkuboTest.perfectHash();
        bytes memory fills = abi.encodePacked(
            uint16(10_000),
            bytes1(0x01),
            address(toToken()),
            ekuboPoolConfig(),
            uint256(0)
        );
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig)),
            abi.encodeCall(
                ISettlerActions.EKUBO, (FROM, address(fromToken()), 10_000, false, hashMul, hashMod, fills, 0)
            )
        );
        
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
}
