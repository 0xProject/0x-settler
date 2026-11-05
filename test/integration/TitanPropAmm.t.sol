// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {GasSnapshot} from "@forge-gas-snapshot/GasSnapshot.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";

import {IAllowanceHolder} from "src/allowanceholder/IAllowanceHolder.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {MainnetSettler} from "src/chains/Mainnet/TakerSubmitted.sol";
import {SafeTransferLib} from "src/vendor/SafeTransferLib.sol";

/// Titan's maker interface: the caller transfers `amountIn` to the venue, then calls `swap`.
interface IPropAMM {
    function swap(
        address tokenIn,
        address tokenOut,
        uint256 amountIn,
        uint256 minAmountOut,
        address recipient,
        uint256 deadline
    ) external returns (uint256 amountOut);
}

/// @dev Each case forks mainnet just before a real fill through Titan's router, so the maker's
/// price update for that block is already applied, and the taker sells the same amount through
/// AllowanceHolder and Settler.
contract TitanPropAmmTest is Test, GasSnapshot {
    using SafeTransferLib for IERC20;

    uint256 private constant BASIS = 1_000_000;
    IAllowanceHolder private constant ALLOWANCE_HOLDER = IAllowanceHolder(0x0000000000001fF3684f28c67538d4D072C22734);
    IERC20 private constant WETH = IERC20(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2);
    IERC20 private constant USDC = IERC20(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48);
    IERC20 private constant USDT = IERC20(0xdAC17F958D2ee523a2206206994597C13D831ec7);
    address private constant TAKER = address(0x7a4e5);

    MainnetSettler private settler;

    struct Fill {
        bytes32 txHash;
        address venue;
        IERC20 tokenIn;
        IERC20 tokenOut;
        uint256 amountIn;
        uint256 amountOut; // from the router's `Swapped` event
    }

    function _fork(Fill memory fill) private {
        vm.createSelectFork("mainnet", fill.txHash);
        vm.setEvmVersion("osaka");
        vm.chainId(31337);
        settler = new MainnetSettler(bytes20(0));
        vm.chainId(1);
        // Settler keeps 1 wei of each token, so seed it like a deployed Settler.
        deal(address(fill.tokenIn), address(settler), 1);
        deal(address(fill.tokenOut), address(settler), 1);
        deal(address(fill.tokenIn), TAKER, fill.amountIn);
        vm.prank(TAKER);
        fill.tokenIn.safeApprove(address(ALLOWANCE_HOLDER), type(uint256).max);
    }

    function _execute(Fill memory fill, bytes memory action, string memory snap) private returns (uint256 out) {
        ISignatureTransfer.PermitTransferFrom memory permit;
        permit.permitted.token = address(fill.tokenIn);
        permit.permitted.amount = fill.amountIn;
        permit.deadline = block.timestamp;
        bytes[] memory actions = new bytes[](2);
        actions[0] = abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, new bytes(0)));
        actions[1] = action;
        bytes memory data = abi.encodeCall(
            settler.execute,
            (
                ISettlerBase.AllowedSlippage({recipient: payable(TAKER), buyToken: fill.tokenOut, minAmountOut: 1}),
                actions,
                bytes32(0)
            )
        );

        uint256 before = fill.tokenOut.balanceOf(TAKER);
        vm.startPrank(TAKER, TAKER);
        if (bytes(snap).length != 0) snapStart(snap);
        ALLOWANCE_HOLDER.exec(address(settler), address(fill.tokenIn), fill.amountIn, payable(address(settler)), data);
        if (bytes(snap).length != 0) snapEnd();
        vm.stopPrank();
        out = fill.tokenOut.balanceOf(TAKER) - before;
        assertEq(fill.tokenIn.balanceOf(TAKER), 0, "taker input spent");
        assertEq(fill.tokenIn.balanceOf(address(settler)), 1, "input fully sold");
    }

    function _push(Fill memory fill) private view returns (bytes memory) {
        bytes memory swap = abi.encodeCall(
            IPropAMM.swap, (address(fill.tokenIn), address(fill.tokenOut), 0, 0, address(settler), block.timestamp)
        );
        // `amountIn` is the third word after the selector
        return abi.encodeCall(ISettlerActions.BASIC_PUSH, (address(fill.tokenIn), BASIS, fill.venue, 0x44, swap));
    }

    function _check(Fill memory fill, string memory snap) private {
        _fork(fill);
        assertEq(_execute(fill, _push(fill), snap), fill.amountOut, "output matches the on-chain fill");
    }

    function _kipseli() private pure returns (Fill memory) {
        return Fill(
            0x0e0ec86c89c92803fb893a361d35a25c40971de88f4b78f3348a330fc14d7547,
            0x71e790dd841c8A9061487cb3E78C288E75cE0B3d,
            USDC,
            WETH,
            38090391587,
            16275738422600551969
        );
    }

    function testKipseli_usdcToWeth() public {
        _check(_kipseli(), "allowanceHolder_basicPush_kipseli_USDC-WETH");
    }

    function testBopAmm_wethToUsdc() public {
        _check(
            Fill(
                0x9db87c2fccc7b079ba818c916ba0b59dbf34f0dd32c561468bd4c61d39467438,
                0xB09AAA8933626d7E4C48D65dAd2D77021CFBCA9a,
                WETH,
                USDC,
                636992272156649468,
                1537370489
            ),
            "allowanceHolder_basicPush_bopAmm_WETH-USDC"
        );
    }

    // USDT's `transfer` returns nothing.
    function testUsdtIn() public {
        _check(
            Fill(
                0x0e81ee5cc1b937ade579be477b8ef0579b64c44c616e5e9724ac6b7016e6b341,
                0x5979458912F80B96d30D4220af8E2e4925A33320,
                USDT,
                WETH,
                37249149019,
                16372396188334286947
            ),
            "allowanceHolder_basicPush_USDT-WETH"
        );
    }

    // The USDC/WETH 0.05% UniswapV3 pool. USDC is token0, so the price limit is the minimum.
    function _uniswapV3(Fill memory fill) private view returns (bytes memory) {
        bytes memory path = abi.encodePacked(fill.tokenIn, uint8(0), uint24(500), uint160(4295128740), fill.tokenOut);
        return abi.encodeCall(ISettlerActions.UNISWAPV3, (address(settler), BASIS, path, 0));
    }

    // Kipseli first, falling back to UniswapV3.
    function _select(Fill memory fill) private view returns (bytes memory) {
        bytes[][] memory candidates = new bytes[][](2);
        candidates[0] = new bytes[](1);
        candidates[0][0] = _push(fill);
        candidates[1] = new bytes[](1);
        candidates[1][0] = _uniswapV3(fill);
        uint256[] memory targets = new uint256[](2);
        targets[0] = fill.amountOut;
        return abi.encodeCall(ISettlerActions.SELECT, (600_000, address(fill.tokenOut), targets, candidates));
    }

    function testSelect_freshQuote_commitsTitan() public {
        Fill memory fill = _kipseli();
        _fork(fill);
        assertEq(_execute(fill, _select(fill), ""), fill.amountOut, "Titan candidate committed");
    }

    function testSelect_staleQuote_fallsBack() public {
        Fill memory fill = _kipseli();
        _fork(fill);
        // One second later the maker's update no longer matches `block.timestamp`, so the venue reverts.
        vm.warp(block.timestamp + 1);
        uint256 snap = vm.snapshotState();
        uint256 fallbackOut = _execute(fill, _uniswapV3(fill), "");
        vm.revertToState(snap);

        // The reverted candidate's push is undone, so the fallback sells the whole input.
        assertEq(_execute(fill, _select(fill), ""), fallbackOut, "fallback committed");
    }
}
