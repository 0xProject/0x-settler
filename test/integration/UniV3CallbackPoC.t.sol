// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {MainnetSettler as Settler} from "src/chains/Mainnet/TakerSubmitted.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {IUniswapV3Pool} from "src/core/UniswapV3Fork.sol";
import {AddressDerivation} from "src/utils/AddressDerivation.sol";

import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {uniswapV3MainnetFactory} from "src/core/univ3forks/UniswapV3.sol";

import {Utils} from "../unit/Utils.sol";
import {Permit2Signature} from "../utils/Permit2Signature.sol";
import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";

import {MockERC20} from "@solmate/test/utils/mocks/MockERC20.sol";

import {MainnetDefaultFork} from "./BaseForkTest.t.sol";

contract UniswapV3PoolDummy {
    MockERC20 token0;
    MockERC20 token1;
    int256 amount0;
    int256 amount1;

    function setSwapData(MockERC20 token0_, MockERC20 token1_, int256 amount0_, int256 amount1_) public {
        token0 = token0_;
        token1 = token1_;
        amount0 = amount0_;
        amount1 = amount1_;
    }

    fallback(bytes calldata) external returns (bytes memory) {
        (address recipient,,,, bytes memory data) = abi.decode(msg.data[4:], (address, bool, int256, uint160, bytes));
        (bool ok,) = msg.sender
            .call(abi.encodeWithSignature("uniswapV3SwapCallback(int256,int256,bytes)", amount0, amount1, data));
        require(ok, "UniV3Callback failure");
        if (amount0 < 0) token0.transfer(recipient, uint256(-amount0));
        if (amount1 < 0) token1.transfer(recipient, uint256(-amount1));
        return abi.encode(amount0, amount1);
    }
}

contract Shim {
    // forgefmt: disable-next-line
    function chainId() external returns (uint256) { // this is non-view (mutable) on purpose
        return block.chainid;
    }
}

contract UniV3CallbackPoC is Utils, Permit2Signature, MainnetDefaultFork {
    address internal constant ETH = 0xEeeeeEeeeEeEeeEeEeEeeEEEeeeeEeeeeeeeEEeE;

    ISignatureTransfer permit2 = ISignatureTransfer(0x000000000022D473030F116dDEE9F6B43aC78BA3);
    bytes32 internal permit2Domain;

    Settler settler;
    address pool;

    address dai;
    address token;
    address payable alice;
    uint256 alicePk;
    address payable bob;

    function setUp() public {
        vm.createSelectFork(_testChainId(), _testBlockNumber());
        vm.setEvmVersion("osaka");

        address alice_;
        (alice_, alicePk) = makeAddrAndKey("Alice");
        alice = payable(alice_);
        bob = payable(makeAddr("Bob"));

        // Deploy dummy tokens
        dai = address(new MockERC20("DAI", "DAI", 18));
        token = address(new MockERC20("TKN", "TKN", 18));

        vm.label(dai, "DAI");
        vm.label(token, "TKN");

        permit2Domain = permit2.DOMAIN_SEPARATOR();

        // Deploy Settler.
        {
            uint256 forkChainId = (new Shim()).chainId();
            vm.chainId(31337);
            settler = new Settler(bytes20(0));
            vm.chainId(forkChainId);
        }

        // Deploy dummy pool.
        pool = _toPool(token, 500, dai);
        vm.etch(pool, type(UniswapV3PoolDummy).runtimeCode);

        // Give pool some tokens.
        MockERC20(dai).mint(pool, 100 ether);
        MockERC20(token).mint(pool, 100 ether);
    }

    function _toPool(address inputToken, uint24 fee, address outputToken) private view returns (address) {
        (address token0, address token1) =
            inputToken < outputToken ? (inputToken, outputToken) : (outputToken, inputToken);
        bytes32 salt;
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(0x00, token0)
            mstore(0x20, token1)
            mstore(0x40, fee)
            salt := keccak256(0x00, 0x60)
            mstore(0x40, ptr)
        }
        return AddressDerivation.deriveDeterministicContract(
            uniswapV3MainnetFactory, salt, 0xe34f199b19b2b4f47f68442619d555527d244f78a3297ea89325f843f87b8b54
        );
    }

    function sqrtPriceLimitX96(IERC20 sellToken, IERC20 buyToken) internal view virtual returns (uint160) {
        bool zeroForOne = (sellToken == IERC20(ETH)) || ((buyToken != IERC20(ETH)) && (sellToken < buyToken));
        return zeroForOne ? 4295128740 : 1461446703485210103287273052203988822378723970341;
    }

    function testUniswapV3CallbackFrontRun() public {
        MockERC20(dai).mint(alice, 100e18);

        vm.prank(alice);
        MockERC20(dai).approve(address(permit2), type(uint256).max);

        uint256 amount = 777;
        ISignatureTransfer.PermitTransferFrom memory permit = defaultERC20PermitTransfer(dai, amount, 1);
        bytes memory sig = getPermitTransferSignature(permit, address(settler), alicePk, permit2Domain);

        uint24 fee = 500;
        bytes memory uniswapV3Path =
            abi.encodePacked(uint8(0), fee, sqrtPriceLimitX96(IERC20(dai), IERC20(token)), token);

        uint256 poolAmountOut = 5555;
        bool zeroForOne = dai < token;
        UniswapV3PoolDummy(pool)
            .setSwapData(
                MockERC20(zeroForOne ? dai : token),
                MockERC20(zeroForOne ? token : dai),
                zeroForOne ? int256(amount) : -int256(poolAmountOut),
                zeroForOne ? -int256(poolAmountOut) : int256(amount)
            );

        bytes memory uniswapV3CallbackData = abi.encodePacked(
            address(0), permit.permitted.token, permit.permitted.amount, permit.nonce, permit.deadline, false, sig
        );
        bytes memory poolCalldata = abi.encodeCall(
            IUniswapV3Pool.swap,
            (
                address(settler), // recipient
                false, // unused
                0, // unused
                0, // unused
                uniswapV3CallbackData
            )
        );
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(
                ISettlerActions.BASIC,
                (
                    address(0), // sellToken
                    1_000_000, // proportion
                    pool, // pool
                    0, // offset
                    poolCalldata
                )
            )
        );

        Settler.AllowedSlippage memory slippage;
        slippage.recipient = bob;
        slippage.buyToken = IERC20(token);
        slippage.minAmountOut = poolAmountOut;
        uint256 aliceSellBalance = MockERC20(dai).balanceOf(alice);
        uint256 bobBuyBalance = MockERC20(token).balanceOf(bob);

        vm.startPrank(bob);
        vm.expectRevert("UniV3Callback failure");
        settler.execute(slippage, actions, bytes32(0));
        vm.stopPrank();

        assertEq(MockERC20(dai).balanceOf(alice), aliceSellBalance);
        assertEq(MockERC20(token).balanceOf(bob), bobBuyBalance);

        actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.UNISWAPV3_VIP, (alice, permit, uniswapV3Path, sig, 100))
        );
        Settler.AllowedSlippage memory noSlippage;
        vm.prank(alice);
        settler.execute(noSlippage, actions, bytes32(0));

        assertEq(MockERC20(dai).balanceOf(alice), aliceSellBalance - amount);
        assertEq(MockERC20(token).balanceOf(alice), poolAmountOut);
    }
}
