// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {GasSnapshot} from "@forge-gas-snapshot/GasSnapshot.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";

import {ALLOWANCE_HOLDER} from "src/allowanceholder/IAllowanceHolder.sol";
import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {MainnetSettler} from "src/chains/Mainnet/TakerSubmitted.sol";
import {PropAmmMux, IPropAMM} from "src/PropAmmMux.sol";
import {SafeTransferLib} from "src/vendor/SafeTransferLib.sol";

IERC20 constant WETH = IERC20(0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2);
IERC20 constant USDC = IERC20(0xA0b86991c6218b36c1d19D4a2e9Eb0cE3606eB48);
IERC20 constant USDT = IERC20(0xdAC17F958D2ee523a2206206994597C13D831ec7);

IPropAMM constant KIPSELI  = IPropAMM(0x71e790dd841c8A9061487cb3E78C288E75cE0B3d);
IPropAMM constant TEMPEST  = IPropAMM(0x00000003f1ec2379e79F58E12EC6C4F51Ee92149);
IPropAMM constant GOLIATH  = IPropAMM(0x4367985A63063fc970b009c6E599e9225181f551);
IPropAMM constant STELAXIS = IPropAMM(0x77047Af6CD8f7f84d96A020a2833d24916b75FDE);
IPropAMM constant NO_PRIMARY = IPropAMM(address(0));

/// @dev Mainnet fork tests of `PropAmmMux` behind `MainnetSettler`, `ALLOWANCE_HOLDER`, and `SELECT`.
contract PropAmmMuxIntegrationTest is Test, GasSnapshot {
    using SafeTransferLib for IERC20;

    uint256 internal constant BASIS = 1_000_000;
    address private constant TAKER = address(0x7a4e5);
    address payable private constant FEE_RECIPIENT = payable(address(0xfee));

    MainnetSettler internal settler;
    PropAmmMux internal mux;

    function _setupAtBlock(uint256 blockNumber, IERC20 tokenIn, IERC20 tokenOut, uint256 amountIn) internal {
        vm.createSelectFork("mainnet", blockNumber);
        vm.setEvmVersion("osaka");
        vm.chainId(31337);
        settler = new MainnetSettler(bytes20(0));
        mux = new PropAmmMux();
        vm.chainId(1);

        deal(address(tokenIn), address(settler), 1);
        deal(address(tokenOut), address(settler), 1);
        deal(address(tokenIn), TAKER, amountIn);
        vm.prank(TAKER);
        tokenIn.safeApprove(address(ALLOWANCE_HOLDER), type(uint256).max);
    }

    function _execute(IERC20 tokenIn, IERC20 tokenOut, uint256 amountIn, bytes[] memory extraActions, bool snap)
        internal
        returns (uint256 out)
    {
        address payable target = payable(address(settler));
        ISignatureTransfer.PermitTransferFrom memory permit;
        permit.permitted.token = address(tokenIn);
        permit.permitted.amount = amountIn;
        permit.deadline = block.timestamp;

        bytes[] memory actions = new bytes[](1 + extraActions.length);
        actions[0] = abi.encodeCall(ISettlerActions.TRANSFER_FROM, (target, permit, new bytes(0)));
        for (uint256 i; i < extraActions.length; ++i) {
            actions[1 + i] = extraActions[i];
        }
        bytes memory data = abi.encodeCall(
            settler.execute,
            (
                ISettlerBase.AllowedSlippage({recipient: payable(TAKER), buyToken: tokenOut, minAmountOut: 1}),
                actions,
                bytes32(0)
            )
        );

        uint256 before = tokenOut.balanceOf(TAKER);
        vm.prank(TAKER, TAKER);
        if (snap) snapStart("allowanceHolder_propAmmMux_primaryHit");
        ALLOWANCE_HOLDER.exec(target, address(tokenIn), amountIn, target, data);
        if (snap) snapEnd();
        out = tokenOut.balanceOf(TAKER) - before;
        assertEq(tokenIn.balanceOf(TAKER), 0, "taker input spent");
        assertEq(tokenIn.balanceOf(target), 1, "settler keeps 1 wei");
    }

    function _executeOne(IERC20 tokenIn, IERC20 tokenOut, uint256 amountIn, bytes memory action, bool snap)
        internal
        returns (uint256)
    {
        bytes[] memory extra = new bytes[](1);
        extra[0] = action;
        return _execute(tokenIn, tokenOut, amountIn, extra, snap);
    }

    function _basicMux(
        IERC20 tokenIn,
        IERC20 tokenOut,
        uint256 minOut,
        IPropAMM primary,
        IPropAMM[] memory backups
    ) internal view returns (bytes memory) {
        bytes memory callData = abi.encodeCall(
            PropAmmMux.swap, (tokenIn, tokenOut, 0, minOut, address(settler), type(uint256).max, primary, backups)
        );
        // `amountIn` is the third word after the selector (0x44)
        return abi.encodeCall(ISettlerActions.BASIC, (address(tokenIn), BASIS, address(mux), 0x44, callData));
    }

    function _venues(IPropAMM a, IPropAMM b, IPropAMM c) internal pure returns (IPropAMM[] memory vs) {
        vs = new IPropAMM[](3);
        vs[0] = a;
        vs[1] = b;
        vs[2] = c;
    }

    function _venues4(IPropAMM a, IPropAMM b, IPropAMM c, IPropAMM d) internal pure returns (IPropAMM[] memory vs) {
        vs = new IPropAMM[](4);
        vs[0] = a;
        vs[1] = b;
        vs[2] = c;
        vs[3] = d;
    }

    function _uniV3UsdcToWeth() internal view returns (bytes memory) {
        bytes memory path = abi.encodePacked(USDC, uint8(0), uint24(500), uint160(4295128740), WETH);
        return abi.encodeCall(ISettlerActions.UNISWAPV3, (address(settler), BASIS, path, 0));
    }

    /// Block 26486293: Goliath is inactive, Stelaxis and Kipseli are live; primary fails over to
    /// Stelaxis and post-SELECT `POSITIVE_SLIPPAGE` collects surplus above the hurdle.
    function testSelect_primaryInactive_recoversBestBackupAndSurplus() public {
        uint256 amountIn = 6_954_542_247;
        _setupAtBlock(26_486_293, USDC, WETH, amountIn);

        uint256 relaxedTarget = 4_163_118_879_178_607_314;
        uint256 hurdle = 4_165_000_000_000_000_000;
        uint256 stelaxisQuote = STELAXIS.quote(USDC, WETH, amountIn);
        uint256 kipseliQuote = KIPSELI.quote(USDC, WETH, amountIn);
        assertGt(stelaxisQuote, kipseliQuote);

        IPropAMM[] memory backups = _venues(KIPSELI, STELAXIS, TEMPEST);
        bytes[][] memory candidates = new bytes[][](2);
        candidates[0] = new bytes[](1);
        candidates[0][0] = _basicMux(USDC, WETH, relaxedTarget, GOLIATH, backups);
        candidates[1] = new bytes[](1);
        candidates[1][0] = _uniV3UsdcToWeth();

        uint256[] memory targets = new uint256[](2);
        targets[0] = relaxedTarget;

        bytes[] memory actions = new bytes[](2);
        actions[0] = abi.encodeCall(ISettlerActions.SELECT, (500_000, address(WETH), targets, candidates));
        actions[1] = abi.encodeCall(
            ISettlerActions.POSITIVE_SLIPPAGE, (FEE_RECIPIENT, address(WETH), hurdle, BASIS, BASIS)
        );

        uint256 feeBefore = WETH.balanceOf(FEE_RECIPIENT);
        uint256 takerOut = _execute(USDC, WETH, amountIn, actions, false);
        uint256 feeOut = WETH.balanceOf(FEE_RECIPIENT) - feeBefore;
        assertEq(takerOut, hurdle, "taker receives hurdle");
        assertEq(takerOut + feeOut, stelaxisQuote, "total equals best live backup quote");
    }

    /// Block 26486293 warped +12s: all venues are stale, `PropAmmMux` reverts, and `SELECT` commits UniV3.
    function testSelect_allVenuesStale_commitsFallback() public {
        uint256 amountIn = 6_954_542_247;
        _setupAtBlock(26_486_293, USDC, WETH, amountIn);
        vm.warp(block.timestamp + 12);
        vm.roll(block.number + 1);

        uint256 snap = vm.snapshotState();
        uint256 fallbackOut = _executeOne(USDC, WETH, amountIn, _uniV3UsdcToWeth(), false);
        vm.revertToState(snap);

        bytes[][] memory candidates = new bytes[][](2);
        candidates[0] = new bytes[](1);
        candidates[0][0] = _basicMux(USDC, WETH, fallbackOut, NO_PRIMARY, _venues4(GOLIATH, KIPSELI, STELAXIS, TEMPEST));
        candidates[1] = new bytes[](1);
        candidates[1][0] = _uniV3UsdcToWeth();

        uint256[] memory targets = new uint256[](2);
        targets[0] = fallbackOut;

        bytes memory selectAction = abi.encodeCall(ISettlerActions.SELECT, (500_000, address(WETH), targets, candidates));
        assertEq(_executeOne(USDC, WETH, amountIn, selectAction, false), fallbackOut, "fallback committed");
    }

    /// Block 26485859: `swapBest` mode (`primary == 0`) picks the max live quote across all venues.
    function testSwapBest_multiLive_picksHighestQuote() public {
        uint256 amountIn = 5 ether;
        _setupAtBlock(26_485_859, WETH, USDC, amountIn);

        IPropAMM[] memory venues = _venues4(TEMPEST, KIPSELI, GOLIATH, STELAXIS);
        uint256 expectedMax;
        for (uint256 i; i < venues.length; ++i) {
            try venues[i].quote(WETH, USDC, amountIn) returns (uint256 q) {
                if (q > expectedMax) expectedMax = q;
            } catch {}
        }
        assertGt(expectedMax, 0);

        uint256 out = _executeOne(WETH, USDC, amountIn, _basicMux(WETH, USDC, 1, NO_PRIMARY, venues), false);
        assertEq(out, expectedMax, "picked highest live quote");
    }

    /// Steady-state primary-hit gas measurement with Settler already holding max approval to mux.
    function testPrimaryHit_steadyStateGas() public {
        uint256 amountIn = 5 ether;
        _setupAtBlock(26_485_859, WETH, USDC, amountIn);
        vm.prank(address(settler));
        WETH.safeApprove(address(mux), type(uint256).max);

        // Snapshot before quoting so Goliath's account and storage stay cold for the measured swap.
        uint256 coldSnap = vm.snapshotState();
        uint256 expected = GOLIATH.quote(WETH, USDC, amountIn);
        vm.revertToState(coldSnap);

        bytes memory action = _basicMux(WETH, USDC, 1, GOLIATH, _venues(KIPSELI, STELAXIS, TEMPEST));
        assertEq(_executeOne(WETH, USDC, amountIn, action, true), expected, "primary filled directly");
    }

    /// USDT-in verifies void-return `transferFrom` + Settler `safeApproveIfBelow` on a mainnet fork.
    function testUsdtIn_failsOverFromGoliathToKipseli() public {
        uint256 amountIn = 1_000_000_000;
        _setupAtBlock(26_486_239, USDT, USDC, amountIn);

        vm.expectRevert("invalid pair");
        GOLIATH.quote(USDT, USDC, amountIn);
        uint256 expected = KIPSELI.quote(USDT, USDC, amountIn);
        assertEq(expected, 998_905_807);

        IPropAMM[] memory backups = new IPropAMM[](1);
        backups[0] = KIPSELI;
        uint256 out = _executeOne(USDT, USDC, amountIn, _basicMux(USDT, USDC, 990_000_000, GOLIATH, backups), false);
        assertEq(out, expected, "USDT-in filled via Kipseli");
    }
}
