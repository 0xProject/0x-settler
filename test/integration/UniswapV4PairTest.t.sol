// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {IAllowanceTransfer} from "@permit2/interfaces/IAllowanceTransfer.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";

import {Settler} from "src/Settler.sol";
import {NotesLib} from "src/core/FlashAccountingCommon.sol";
import {UnsafeMath} from "src/utils/UnsafeMath.sol";

import {UNIVERSAL_ROUTER, encodePermit2Permit, encodeV4Swap} from "src/vendor/IUniswapUniversalRouter.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";

import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";

abstract contract UniswapV4PairTest is SettlerBasePairTest {
    using UnsafeMath for uint256;

    function uniswapV4PerfectHash(IERC20 fromTokenCompat, IERC20 toTokenCompat) internal view virtual returns (uint256 hashMod, uint256 hashMul) {
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

    function uniswapV4FeeTier() internal view virtual returns (uint24) {
        return 500;
    }

    function uniswapV4TickSpacing() internal view virtual returns (int24) {
        return 10;
    }

    function uniswapV4Hook() internal view virtual returns (address) {
        return address(0);
    }

    function _canonicalize(IERC20 token) private pure returns (IERC20) {
        if (token == IERC20(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2)) {
            return IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE);
        }
        return token;
    }

    function testUniswapV4UniversalRouter() public {
        bytes memory commands = new bytes(2);
        bytes[] memory inputs = new bytes[](2);

        IAllowanceTransfer.PermitSingle memory permit = defaultERC20PermitSingle(address(fromToken()), PERMIT2_FROM_NONCE);
        bytes memory signature = getPermitSingleSignature(permit, address(UNIVERSAL_ROUTER), FROM_PRIVATE_KEY, permit2Domain);

        (commands[0], inputs[0]) = encodePermit2Permit(fromToken(), PERMIT2_FROM_NONCE, signature);
        IERC20 fromTokenCompat = _canonicalize(fromToken());
        IERC20 toTokenCompat = _canonicalize(toToken());
        (commands[1], inputs[1]) = encodeV4Swap(FROM, amount(), 0 wei, fromTokenCompat, uniswapV4FeeTier(), uniswapV4TickSpacing(), uniswapV4Hook(), toTokenCompat);

        (bool success, ) = FROM.call(""); // touch FROM to warm it; in normal operation this would already be warmed
        require(success);

        vm.startPrank(FROM, FROM);
        snapStartName("universalRouter_uniswapV4");
        UNIVERSAL_ROUTER.execute(commands, inputs, block.timestamp);
        snapEnd();
        vm.stopPrank();
    }

    function testSettler_uniswapV4VIP_toNative() public {
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _getDefaultFromPermit2();

        IERC20 fromTokenCompat = _canonicalize(fromToken());
        IERC20 toTokenCompat = _canonicalize(toToken());
        vm.assume(toTokenCompat == IERC20(0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE));
        assertEq(permit.permitted.token, address(fromTokenCompat));

        (uint256 hashMul, uint256 hashMod) = uniswapV4PerfectHash(fromTokenCompat, toTokenCompat);
        bytes memory fills = abi.encodePacked(uint16(10_000), bytes1(0x01), toTokenCompat, uniswapV4FeeTier(), uniswapV4TickSpacing(), uniswapV4Hook(), uint24(0), "");
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.UNISWAPV4_VIP, (FROM, false, hashMul, hashMod, fills, permit, sig, 0 wei))
        );
        ISettlerBase.AllowedSlippage memory slippage =
            ISettlerBase.AllowedSlippage({recipient: payable(address(0)), buyToken: IERC20(address(0)), minAmountOut: 0 ether});

        Settler _settler = settler;
        vm.startPrank(FROM);
        snapStartName("settler_uniswapV4VIP_toNative");
        _settler.execute(slippage, actions, bytes32(0));
        snapEnd();
    }
}
