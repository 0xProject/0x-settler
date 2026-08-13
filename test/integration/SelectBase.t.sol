// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {BaseSettler} from "src/chains/Base/TakerSubmitted.sol";

import {ActionDataBuilder} from "../utils/ActionDataBuilder.sol";
import {SettlerBasePairTest} from "./SettlerBasePairTest.t.sol";

contract SelectBase is SettlerBasePairTest {
    uint256 internal constant BASE_BLOCK = 48_241_765;
    address payable internal RECIPIENT = payable(makeAddr("recipient"));
    uint256 internal constant AMOUNT = 0.01 ether;
    uint256 internal constant SELECT_GAS_CAP = 400_000;

    IERC20 internal constant BASE_WETH = IERC20(0x4200000000000000000000000000000000000006);
    IERC20 internal constant USDC = IERC20(0x833589fCD6eDb6E08f4c7C32D4f71b54bdA02913);

    uint8 internal constant UNISWAP_V3_FORK_ID = 0;
    uint8 internal constant AERODROME_V3_FORK_ID = 4;
    uint24 internal constant UNISWAP_V3_FEE = 500;
    uint24 internal constant AERODROME_TICK_SPACING = 100;
    uint160 internal constant SQRT_PRICE_LIMIT_X96 = 4295128740;

    function setUp() public override {
        super.setUp();
        // The pinned account has delegated code at this block. Signatures here expect an EOA.
        vm.etch(FROM, bytes(""));
        vm.label(RECIPIENT, "RECIPIENT");
        safeApproveIfBelow(BASE_WETH, FROM, address(PERMIT2), AMOUNT);
    }

    function settlerInitCode() internal pure override returns (bytes memory) {
        return bytes.concat(type(BaseSettler).creationCode, abi.encode(bytes20(0)));
    }

    function _testChainId() internal pure override returns (string memory) {
        return "base";
    }

    function _testBlockNumber() internal pure override returns (uint256) {
        return BASE_BLOCK;
    }

    function _testName() internal pure override returns (string memory) {
        return "BASE-SELECT";
    }

    function fromToken() internal pure override returns (IERC20) {
        return BASE_WETH;
    }

    function toToken() internal pure override returns (IERC20) {
        return USDC;
    }

    function amount() internal pure override returns (uint256) {
        return AMOUNT;
    }

    function testFallbackRescue_primaryRevert_commitsAlternate() public {
        bytes[][] memory candidates = _twoCandidates(type(uint256).max, 0);
        uint256[] memory targets = new uint256[](2);

        uint256 beforeBalance = USDC.balanceOf(RECIPIENT);
        snapStartName("settler_selectFallbackRescue");
        _runSelect(address(0), targets, candidates, 1);
        snapEnd();
        uint256 received = USDC.balanceOf(RECIPIENT) - beforeBalance;

        assertGt(received, 1, "alternate route paid recipient");
        assertEq(BASE_WETH.balanceOf(address(settler)), 0, "settler WETH consumed");
        assertEq(USDC.balanceOf(address(settler)), 0, "top-level slippage transferred USDC");
    }

    function testFirstCandidateSuccess_commitsImmediately() public {
        bytes[][] memory candidates = _twoCandidates(0, 0);
        uint256 beforeBalance = USDC.balanceOf(RECIPIENT);

        snapStartName("settler_selectFirstCandidate");
        _runSelect(address(0), new uint256[](2), candidates, 1);
        snapEnd();

        assertGt(USDC.balanceOf(RECIPIENT) - beforeBalance, 1, "first candidate paid recipient");
    }

    function testAllReservationsMiss_reverts() public {
        bytes[][] memory candidates = _twoCandidates(0, 0);
        uint256[] memory targets = new uint256[](2);
        targets[0] = type(uint256).max;
        targets[1] = type(uint256).max;

        uint256 beforeBalance = USDC.balanceOf(RECIPIENT);
        vm.expectRevert();
        _runSelect(address(USDC), targets, candidates, 0);

        assertEq(USDC.balanceOf(RECIPIENT), beforeBalance, "no candidate committed");
    }

    function testLadderCommit_unreachableFirstTarget_commitsReachableSecondTarget() public {
        bytes[][] memory candidates = _twoCandidates(0, 0);
        uint256 aerodromeOutput = _standaloneOutput(candidates[1]);

        uint256[] memory targets = new uint256[](2);
        targets[0] = type(uint256).max;
        targets[1] = aerodromeOutput;

        uint256 beforeBalance = USDC.balanceOf(RECIPIENT);
        snapStartName("settler_selectLadderCommit");
        _runSelect(address(USDC), targets, candidates, aerodromeOutput);
        snapEnd();
        uint256 received = USDC.balanceOf(RECIPIENT) - beforeBalance;

        assertEq(received, aerodromeOutput, "first reachable rung committed");
    }

    function _runSelect(address token, uint256[] memory targets, bytes[][] memory candidates, uint256 minOut) internal {
        bytes[] memory actions = ActionDataBuilder.build(
            _getDefaultFromPermit2Action(),
            abi.encodeCall(ISettlerActions.SELECT, (SELECT_GAS_CAP, token, targets, candidates))
        );

        _execute(actions, minOut);
    }

    function _standaloneOutput(bytes[] memory candidate) internal returns (uint256 output) {
        uint256 snapshot = vm.snapshotState();
        uint256 beforeBalance = USDC.balanceOf(RECIPIENT);
        _execute(ActionDataBuilder.build(_getDefaultFromPermit2Action(), candidate[0]), 1);
        output = USDC.balanceOf(RECIPIENT) - beforeBalance;
        vm.revertToState(snapshot);
    }

    function _execute(bytes[] memory actions, uint256 minOut) internal {
        vm.prank(FROM, FROM);
        settler.execute(
            ISettlerBase.AllowedSlippage({recipient: RECIPIENT, buyToken: USDC, minAmountOut: minOut}),
            actions,
            bytes32(0)
        );
    }

    function _twoCandidates(uint256 uniswapMinOut, uint256 aerodromeMinOut)
        internal
        view
        returns (bytes[][] memory candidates)
    {
        candidates = new bytes[][](2);
        candidates[0] = _candidate(_path(UNISWAP_V3_FORK_ID, UNISWAP_V3_FEE), uniswapMinOut);
        candidates[1] = _candidate(_path(AERODROME_V3_FORK_ID, AERODROME_TICK_SPACING), aerodromeMinOut);
    }

    function _candidate(bytes memory path, uint256 minOut) internal view returns (bytes[] memory candidate) {
        candidate = new bytes[](1);
        candidate[0] = abi.encodeCall(ISettlerActions.UNISWAPV3, (address(settler), 10_000, path, minOut));
    }

    function _path(uint8 forkId, uint24 poolId) internal pure returns (bytes memory) {
        return abi.encodePacked(address(BASE_WETH), forkId, poolId, SQRT_PRICE_LIMIT_X96, address(USDC));
    }
}
