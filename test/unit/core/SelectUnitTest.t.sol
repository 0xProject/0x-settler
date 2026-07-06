// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {Vm} from "@forge-std/Vm.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";

import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {BaseSettler} from "src/chains/Base/TakerSubmitted.sol";
import {Select} from "src/core/Select.sol";
import {Measured} from "src/core/SettlerErrors.sol";
import {Permit2Signature} from "test/utils/Permit2Signature.sol";

/// @notice Exercises the real `BaseSettler` `SELECT` action: pure fallback, descending ladder,
///         best-of-N with fail-closed measured commits, measurement-spoof degradation, the
///         improvement fee, the win-outright 1x path, and the candidate gas cap (a stalling
///         candidate must not starve the rest). Only the AMM legs are mocked (allowed for unit
///         tests); the contract under test is the production Settler.
contract SelectUnitTest is Test {
    BaseSettler internal settler;
    TestToken internal buy;
    Pool internal p0;
    Pool internal p1;
    Pool internal p2;
    address internal recipient = makeAddr("recipient");
    address internal taker = makeAddr("taker");
    address internal constant FEE_RECEIVER = 0x23030a6124E871F4744Cb9bc14D519b1f033FFe3;

    function setUp() public {
        settler = new BaseSettler(bytes20(0));
        buy = new TestToken();
        p0 = new Pool(buy);
        p1 = new Pool(buy);
        p2 = new Pool(buy);
        buy.mint(address(p0), 1_000 ether);
        buy.mint(address(p1), 1_000 ether);
        buy.mint(address(p2), 1_000 ether);
    }

    function _candidate(address p) internal pure returns (bytes[] memory c) {
        c = new bytes[](1);
        c[0] = abi.encodeCall(ISettlerActions.BASIC, (address(0), 0, p, 0, abi.encodeCall(Pool.swap, ())));
    }

    /// @dev The tag `_select` computes for a candidate: keccak of its `bytes[]` sub-encoding
    ///      (abi.encode(c) minus the leading 0x20 offset word), i.e. what the golf forwards + hashes.
    function _tag(bytes[] memory c) internal pure returns (bytes32 t) {
        bytes memory e = abi.encode(c);
        assembly ("memory-safe") {
            t := and(keccak256(add(e, 0x40), sub(mload(e), 0x20)), not(shl(0xff, 0x01)))
        }
    }

    function _candidates3() internal view returns (bytes[][] memory c) {
        c = new bytes[][](3);
        c[0] = _candidate(address(p0));
        c[1] = _candidate(address(p1));
        c[2] = _candidate(address(p2));
    }

    function _bestOfTargets(uint256 belief) internal pure returns (uint256[] memory targets) {
        targets = new uint256[](3);
        targets[0] = belief;
        targets[1] = type(uint256).max;
        targets[2] = type(uint256).max;
    }

    function _run(
        uint256 shareBps,
        address token,
        uint256[] memory targets,
        bytes[][] memory candidates,
        uint256 minOut
    ) internal {
        uint256[] memory hurdles = new uint256[](candidates.length);
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeWithSelector(
            ISettlerActions.SELECT.selector, shareBps, uint256(0), token, targets, hurdles, candidates
        );
        vm.prank(taker, taker);
        settler.execute(
            ISettlerBase.AllowedSlippage({
                recipient: payable(recipient), buyToken: IERC20(address(buy)), minAmountOut: minOut
            }),
            actions,
            bytes32(0)
        );
    }

    function _runWithGasCap(
        uint256 shareBps,
        uint256 gasCap,
        address token,
        uint256[] memory targets,
        bytes[][] memory candidates,
        uint256 minOut,
        uint256 txGas
    ) internal {
        uint256[] memory hurdles = new uint256[](candidates.length);
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeWithSelector(
            ISettlerActions.SELECT.selector, shareBps, gasCap, token, targets, hurdles, candidates
        );
        vm.prank(taker, taker);
        settler.execute{gas: txGas}(
            ISettlerBase.AllowedSlippage({
                recipient: payable(recipient), buyToken: IERC20(address(buy)), minAmountOut: minOut
            }),
            actions,
            bytes32(0)
        );
    }

    /// @dev ROUTE_OR_FALLBACK personality: token = 0 and zero targets —
    ///      the failing primary is discarded wholesale, the alternate commits.
    function test_fallback_primaryRevert_commitsAlternate() public {
        p0.set(10 ether, true); // delivers, then reverts
        p1.set(7 ether, false);
        _run(0, address(0), new uint256[](3), _candidates3(), 7 ether);
        assertEq(buy.balanceOf(recipient), 7 ether, "alternate's output only (primary rolled back)");
        assertEq(p1.callCount(), 1, "alternate committed");
        assertEq(p2.callCount(), 0, "third candidate never reached");
    }

    /// @dev Descending-floor LADDER personality: rung 0 misses its high floor, rung 1 clears its
    ///      lower floor and commits; rung 2 never runs.
    function test_ladder_firstReachableTargetCommits() public {
        p0.set(8 ether, false);
        p1.set(7 ether, false);
        p2.set(9 ether, false);
        uint256[] memory targets = new uint256[](3);
        targets[0] = 10 ether; // 8 < 10 -> Measured, walk down
        targets[1] = 6 ether; // 7 >= 6 -> commits
        targets[2] = 1;
        _run(0, address(buy), targets, _candidates3(), 7 ether);
        assertEq(buy.balanceOf(recipient), 7 ether, "rung 1 committed");
        assertEq(p2.callCount(), 0, "rung 2 never attempted");
    }

    /// @dev Best-of-N: target missed, all candidates measured and rolled back, argmax committed at
    ///      its measured score (fail-closed).
    function test_measured_bestOfN_commitsArgmax() public {
        p0.set(5 ether, false);
        p1.set(7 ether, false);
        p2.set(9 ether, false);
        uint256[] memory targets = _bestOfTargets(10 ether);
        _run(0, address(buy), targets, _candidates3(), 9 ether);
        assertEq(buy.balanceOf(recipient), 9 ether, "best (p2) committed");
        assertEq(p0.callCount() + p1.callCount(), 0, "losing measurements rolled back");
    }

    /// @dev The improvement fee: shareBps of (winner − runner-up), in the measured token. Winner 9,
    ///      runner-up 7 -> edge 2 -> 50% = 1 to the receiver, 8 to the recipient.
    function test_measured_fee() public {
        p0.set(5 ether, false);
        p1.set(7 ether, false);
        p2.set(9 ether, false);
        uint256[] memory targets = _bestOfTargets(10 ether);
        _run(5_000, address(buy), targets, _candidates3(), 8 ether);
        assertEq(buy.balanceOf(FEE_RECEIVER), 1 ether, "half the measured edge");
        assertEq(buy.balanceOf(recipient), 8 ether, "winner's output minus fee");
    }

    /// @dev Wins outright: 1x, nothing else measured, no fee.
    function test_measured_winsOutright_noFee() public {
        p0.set(10 ether, false);
        uint256[] memory targets = _bestOfTargets(10 ether);
        _run(5_000, address(buy), targets, _candidates3(), 10 ether);
        assertEq(buy.balanceOf(recipient), 10 ether);
        assertEq(p1.callCount() + p2.callCount(), 0, "nothing else measured");
        assertEq(buy.balanceOf(FEE_RECEIVER), 0, "no fee on the outright win");
    }

    /// @dev The tag is computable from public calldata, so an adversarial pool CAN forge
    ///      `Measured(huge, correctTag)` to win selection, then under-deliver on the commit
    ///      (measurements roll back all EVM state, so in production only gas introspection
    ///      distinguishes measure from commit; here a forge env var stands in). The false commit is
    ///      dropped, and SELECT degrades to the real runner-up instead of settling a bad fill.
    function test_measured_spoofCorrectTag_degradesToRunnerUp() public {
        vm.setEnv("SELECT_SPOOF_SEEN", "false");
        p0.set(8 ether, false);
        p2.set(0, false);
        DiscriminatingSpoofPool evil = new DiscriminatingSpoofPool();
        bytes[] memory evilCandidate = _candidate(address(evil));
        bytes32 tag = _tag(evilCandidate);
        evil.setTag(tag);
        uint256[] memory targets = _bestOfTargets(20 ether); // candidate 0 misses -> full runoff
        bytes[][] memory candidates = new bytes[][](3);
        candidates[0] = _candidate(address(p0));
        candidates[1] = evilCandidate;
        candidates[2] = _candidate(address(p2));
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeWithSelector(
            ISettlerActions.SELECT.selector, uint256(0), uint256(0), address(buy), targets, new uint256[](3), candidates
        );
        vm.prank(taker, taker);
        settler.execute(
            ISettlerBase.AllowedSlippage({
                recipient: payable(recipient), buyToken: IERC20(address(buy)), minAmountOut: 8 ether
            }),
            actions,
            bytes32(0)
        );
        assertEq(buy.balanceOf(recipient), 8 ether, "real runner-up settled");
        assertEq(buy.balanceOf(address(evil)), 0, "spoofer delivered nothing");
    }

    /// @dev If every measured candidate diverges during its uncapped commit, the final commit
    ///      failure bubbles to the caller.
    function test_measured_allCommitPhaseCommitsFail_bubblesLastRevert() public {
        vm.setEnv("SELECT_SPOOF_SEEN_0", "false");
        vm.setEnv("SELECT_SPOOF_SEEN_1", "false");
        DiscriminatingSpoofPool evil0 = new DiscriminatingSpoofPool();
        evil0.setKey("SELECT_SPOOF_SEEN_0");
        bytes[] memory evilCandidate0 = _candidate(address(evil0));
        evil0.setTag(_tag(evilCandidate0));
        DiscriminatingSpoofPool evil1 = new DiscriminatingSpoofPool();
        evil1.setKey("SELECT_SPOOF_SEEN_1");
        bytes[] memory evilCandidate1 = _candidate(address(evil1));
        bytes32 tag1 = _tag(evilCandidate1);
        evil1.setTag(tag1);
        uint256[] memory targets = new uint256[](2);
        targets[0] = type(uint256).max;
        targets[1] = type(uint256).max;
        bytes[][] memory candidates = new bytes[][](2);
        candidates[0] = evilCandidate0;
        candidates[1] = evilCandidate1;
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeWithSelector(
            ISettlerActions.SELECT.selector, uint256(0), uint256(0), address(buy), targets, new uint256[](2), candidates
        );
        vm.prank(taker, taker);
        vm.expectRevert(abi.encodeWithSelector(Measured.selector, uint256(0), tag1));
        settler.execute(
            ISettlerBase.AllowedSlippage({
                recipient: payable(recipient), buyToken: IERC20(address(0)), minAmountOut: 0
            }),
            actions,
            bytes32(0)
        );
    }

    /// @dev A dropped spoofer's fake net must not inflate the edge. The committed runner-up p0 (8)
    ///      pays against the real remaining runner-up p2 (7), not the dropped fake 1e30.
    function test_measured_degradedFee_excludesDroppedSpoofer() public {
        vm.setEnv("SELECT_SPOOF_SEEN", "false");
        p0.set(8 ether, false);
        p2.set(7 ether, false);
        DiscriminatingSpoofPool evil = new DiscriminatingSpoofPool();
        bytes[] memory evilCandidate = _candidate(address(evil));
        evil.setTag(_tag(evilCandidate));
        uint256[] memory targets = _bestOfTargets(type(uint256).max);
        bytes[][] memory candidates = new bytes[][](3);
        candidates[0] = _candidate(address(p0));
        candidates[1] = evilCandidate;
        candidates[2] = _candidate(address(p2));
        _run(5_000, address(buy), targets, candidates, 7.5 ether);
        assertEq(buy.balanceOf(FEE_RECEIVER), 0.5 ether, "half the real 1-token edge");
        assertEq(buy.balanceOf(recipient), 7.5 ether, "degraded winner minus fee");
    }

    /// @dev A nested action encoded with length 0..3 underflows `args.length` in
    ///      `CalldataDecoder.decodeCall` (`sub(length, 0x04)` wraps to ~2^256); the guard must catch
    ///      it and revert `ActionInvalid` instead of an OOG/garbage read.
    function testFuzz_shortNestedAction_revertsCleanly(uint256 len) public {
        len = bound(len, 0, 3);
        bytes[] memory actions = new bytes[](1);
        actions[0] = new bytes(len);
        vm.prank(address(settler));
        vm.expectPartialRevert(ActionInvalid.selector);
        Select(address(settler)).executeSelected(actions, IERC20(address(0)), 0, bytes32(0));
    }

    /// @dev The gas cap: a stalling candidate 0 (burns all forwarded gas) must not starve the
    ///      cascade. With `candidateGasLimit` set, the alternate still commits.
    function test_fallback_gasCap_stallingCandidateCannotStarve() public {
        p1.set(7 ether, false);
        bytes[][] memory candidates = new bytes[][](2);
        candidates[0] = _candidate(address(new GasBurnerPool()));
        candidates[1] = _candidate(address(p1));
        uint256[] memory targets = new uint256[](2);
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeWithSelector(
            ISettlerActions.SELECT.selector,
            uint256(0),
            uint256(300_000),
            address(0),
            targets,
            new uint256[](2),
            candidates
        );
        vm.prank(taker, taker);
        settler.execute{gas: 1_500_000}(
            ISettlerBase.AllowedSlippage({
                recipient: payable(recipient), buyToken: IERC20(address(buy)), minAmountOut: 7 ether
            }),
            actions,
            bytes32(0)
        );
        assertEq(buy.balanceOf(recipient), 7 ether, "alternate committed despite the staller");
    }

    function test_fallback_gasCap_lastCandidateRunsUncapped() public {
        GasHeavyPool finisher = new GasHeavyPool(buy);
        finisher.set(7 ether, 9_000);
        buy.mint(address(finisher), 7 ether);
        bytes[][] memory candidates = new bytes[][](3);
        candidates[0] = _candidate(address(new GasBurnerPool()));
        candidates[1] = _candidate(address(new GasBurnerPool()));
        candidates[2] = _candidate(address(finisher));
        uint256[] memory targets = new uint256[](3);
        _runWithGasCap(0, 300_000, address(0), targets, candidates, 7 ether, 1_200_000);
        assertEq(buy.balanceOf(recipient), 7 ether, "final fallback candidate committed");
        assertEq(finisher.callCount(), 1, "final candidate finished during the attempt phase");
    }

    function test_measured_gasGuard_commitsBestSoFar_skippedCandidateExcluded() public {
        p0.set(8 ether, false);
        p2.set(9 ether, false);
        bytes[][] memory candidates = new bytes[][](4);
        candidates[0] = _candidate(address(p0));
        candidates[1] = _candidate(address(new GasBurnerPool()));
        candidates[2] = _candidate(address(new GasBurnerPool()));
        candidates[3] = _candidate(address(p2));
        uint256[] memory targets = new uint256[](4);
        targets[0] = type(uint256).max;
        targets[1] = type(uint256).max;
        targets[2] = type(uint256).max;
        targets[3] = type(uint256).max;
        _runWithGasCap(0, 300_000, address(buy), targets, candidates, 8 ether, 1_150_000);
        assertEq(buy.balanceOf(recipient), 8 ether, "best measured-so-far committed");
        assertEq(p0.callCount(), 1, "measured best committed once");
        assertEq(p2.callCount(), 0, "unmeasured 9-token candidate skipped and excluded");
        assertEq(buy.balanceOf(FEE_RECEIVER), 0, "no fee with zero share");
    }
}

/// @notice Exercises the `SELECT_VIP` spike path against the real Base settler and real Permit2 at
///         its canonical address. Pool legs are mocked only for deterministic local routing.
contract SelectVIPUnitTest is Test, Permit2Signature {
    ISignatureTransfer internal constant PERMIT2 = ISignatureTransfer(0x000000000022D473030F116dDEE9F6B43aC78BA3);
    uint256 internal constant TAKER_PRIVATE_KEY = 0x51e17e;
    uint256 internal constant SELL_AMOUNT = 1 ether;
    uint256 internal constant NONCE = 7;

    BaseSettler internal settler;
    TestToken internal sell;
    TestToken internal buy;
    SelectVIPSellPool internal p0;
    SelectVIPSellPool internal p1;
    address internal recipient = makeAddr("recipient");
    address internal taker = vm.addr(TAKER_PRIVATE_KEY);
    bytes32 internal permit2Domain;

    function setUp() public {
        deployCodeTo("Permit2.sol:Permit2", address(PERMIT2));
        settler = new BaseSettler(bytes20(0));
        sell = new TestToken();
        buy = new TestToken();
        p0 = new SelectVIPSellPool(sell, buy);
        p1 = new SelectVIPSellPool(sell, buy);
        buy.mint(address(p0), 1_000 ether);
        buy.mint(address(p1), 1_000 ether);
        sell.mint(taker, 100 ether);
        vm.prank(taker);
        sell.approve(address(PERMIT2), type(uint256).max);
        permit2Domain = PERMIT2.DOMAIN_SEPARATOR();
    }

    function _permit(uint256 nonce)
        internal
        view
        returns (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig)
    {
        permit = defaultERC20PermitTransfer(address(sell), SELL_AMOUNT, nonce);
        sig = getPermitTransferSignature(permit, address(settler), TAKER_PRIVATE_KEY, permit2Domain);
    }

    function _vipCandidate(address pool, ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig)
        internal
        view
        returns (bytes[] memory c)
    {
        c = new bytes[](2);
        c[0] = abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig));
        c[1] = abi.encodeCall(
            ISettlerActions.BASIC, (address(sell), 10_000, pool, 4, abi.encodeCall(SelectVIPSellPool.swap, (0)))
        );
    }

    function _vipSpoofCandidate(ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig)
        internal
        returns (bytes[] memory c, SelectVIPSpoofPool evil)
    {
        evil = new SelectVIPSpoofPool();
        c = new bytes[](2);
        c[0] = abi.encodeCall(ISettlerActions.TRANSFER_FROM, (address(settler), permit, sig));
        c[1] = abi.encodeCall(
            ISettlerActions.BASIC, (address(sell), 10_000, address(evil), 4, abi.encodeCall(evil.swap, (0)))
        );
    }

    function _tag(bytes[] memory c) internal pure returns (bytes32 t) {
        bytes memory e = abi.encode(c);
        assembly ("memory-safe") {
            t := or(keccak256(add(e, 0x40), sub(mload(e), 0x20)), shl(0xff, 0x01))
        }
    }

    function _runVIP(address token, uint256[] memory targets, bytes[][] memory candidates, uint256 minOut) internal {
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeWithSelector(
            ISettlerActions.SELECT_VIP.selector,
            uint256(0),
            uint256(0),
            token,
            targets,
            new uint256[](candidates.length),
            candidates
        );
        vm.prank(taker, taker);
        settler.execute(
            ISettlerBase.AllowedSlippage({
                recipient: payable(recipient), buyToken: IERC20(address(buy)), minAmountOut: minOut
            }),
            actions,
            bytes32(0)
        );
    }

    function _nonceMask(uint256 nonce) internal pure returns (uint256 wordPos, uint256 mask) {
        wordPos = nonce >> 8;
        mask = 1 << uint8(nonce);
    }

    function _assertNonceSpentOnce(uint256 nonce) internal view {
        (uint256 wordPos, uint256 mask) = _nonceMask(nonce);
        assertEq(PERMIT2.nonceBitmap(taker, wordPos), mask, "Permit2 nonce bit");
    }

    function test_selectVIP_revertedCandidateRollsBackPermitNonce_commitsAlternate() public {
        vm.setEnv("SELECT_VIP_P0_SAW_PULL", "false");
        p0.set(5 ether, true);
        p0.setKey("SELECT_VIP_P0_SAW_PULL");
        p1.set(7 ether, false);
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _permit(NONCE);
        bytes[][] memory candidates = new bytes[][](2);
        candidates[0] = _vipCandidate(address(p0), permit, sig);
        candidates[1] = _vipCandidate(address(p1), permit, sig);

        _runVIP(address(0), new uint256[](2), candidates, 7 ether);

        assertTrue(vm.envBool("SELECT_VIP_P0_SAW_PULL"), "pool A saw the attempted pull");
        assertEq(sell.balanceOf(taker), 99 ether, "taker spent exactly one sell amount");
        _assertNonceSpentOnce(NONCE);
        assertEq(sell.balanceOf(address(p0)), 0, "pool A pull rolled back");
        assertEq(sell.balanceOf(address(p1)), SELL_AMOUNT, "pool B kept the committed pull");
        assertEq(buy.balanceOf(recipient), 7 ether, "alternate committed");
    }

    function test_selectVIP_measurementRollbackUnspendsNonce_onlyWinnerSurvives() public {
        p0.set(5 ether, false);
        p1.set(7 ether, false);
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _permit(NONCE);
        bytes[][] memory candidates = new bytes[][](2);
        candidates[0] = _vipCandidate(address(p0), permit, sig);
        candidates[1] = _vipCandidate(address(p1), permit, sig);
        uint256[] memory targets = new uint256[](2);
        targets[0] = type(uint256).max;
        targets[1] = type(uint256).max;

        _runVIP(address(buy), targets, candidates, 7 ether);

        assertEq(sell.balanceOf(taker), 99 ether, "taker spent exactly one sell amount");
        _assertNonceSpentOnce(NONCE);
        assertEq(sell.balanceOf(address(p0)), 0, "losing measurement pull rolled back");
        assertEq(sell.balanceOf(address(p1)), SELL_AMOUNT, "winner pull survived only on commit");
        assertEq(buy.balanceOf(recipient), 7 ether, "winner output paid");
    }

    function test_selectVIP_replayAfterCommitFailsNonceInvariant() public {
        p0.set(7 ether, false);
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _permit(NONCE);
        bytes[][] memory candidates = new bytes[][](1);
        candidates[0] = _vipCandidate(address(p0), permit, sig);
        uint256[] memory targets = new uint256[](1);

        _runVIP(address(0), targets, candidates, 7 ether);
        _assertNonceSpentOnce(NONCE);

        vm.prank(taker, taker);
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeWithSelector(
            ISettlerActions.SELECT_VIP.selector,
            uint256(0),
            uint256(0),
            address(0),
            targets,
            new uint256[](1),
            candidates
        );
        vm.expectRevert(bytes4(keccak256("InvalidNonce()")));
        settler.execute(
            ISettlerBase.AllowedSlippage({
                recipient: payable(recipient), buyToken: IERC20(address(buy)), minAmountOut: 0
            }),
            actions,
            bytes32(0)
        );
        assertEq(sell.balanceOf(taker), 99 ether, "failed replay did not spend again");
    }

    function test_selectVIP_spoofedMeasurementForfeits_runnerUpCommitsSharedPermitOnce() public {
        vm.setEnv("SELECT_VIP_SPOOF_SEEN", "false");
        p0.set(8 ether, false);
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _permit(NONCE);
        bytes[] memory honest = _vipCandidate(address(p0), permit, sig);
        (bytes[] memory evilCandidate, SelectVIPSpoofPool evil) = _vipSpoofCandidate(permit, sig);
        evil.setTag(_tag(evilCandidate));
        bytes[][] memory candidates = new bytes[][](2);
        candidates[0] = honest;
        candidates[1] = evilCandidate;
        uint256[] memory targets = new uint256[](2);
        targets[0] = type(uint256).max;
        targets[1] = type(uint256).max;

        _runVIP(address(buy), targets, candidates, 8 ether);

        assertEq(sell.balanceOf(taker), 99 ether, "shared permit spent once");
        _assertNonceSpentOnce(NONCE);
        assertEq(sell.balanceOf(address(p0)), SELL_AMOUNT, "runner-up committed");
        assertEq(buy.balanceOf(recipient), 8 ether, "spoof forfeited to runner-up");
    }

    function testGas_selectVIP_oneMeasuredCandidate() public {
        p0.set(7 ether, false);
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _permit(NONCE);
        bytes[][] memory candidates = new bytes[][](1);
        candidates[0] = _vipCandidate(address(p0), permit, sig);
        uint256[] memory targets = new uint256[](1);
        targets[0] = type(uint256).max;
        _runVIP(address(buy), targets, candidates, 7 ether);
    }

    function testGas_selectVIP_twoMeasuredCandidates() public {
        p0.set(5 ether, false);
        p1.set(7 ether, false);
        (ISignatureTransfer.PermitTransferFrom memory permit, bytes memory sig) = _permit(NONCE);
        bytes[][] memory candidates = new bytes[][](2);
        candidates[0] = _vipCandidate(address(p0), permit, sig);
        candidates[1] = _vipCandidate(address(p1), permit, sig);
        uint256[] memory targets = new uint256[](2);
        targets[0] = type(uint256).max;
        targets[1] = type(uint256).max;
        _runVIP(address(buy), targets, candidates, 7 ether);
    }
}

error ActionInvalid(uint256 i, bytes4 action, bytes data);

/// @notice Adversarial leg that behaves differently when measured vs committed. Measurements roll
///         back all EVM state, so a real pool can only discriminate via gas introspection; this test
///         stand-in uses a forge env var (persists across reverts). Measure: forged
///         `Measured(1e30, tag)` with the correct tag. Commit: succeeds delivering nothing.
contract DiscriminatingSpoofPool {
    Vm internal constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    bytes32 internal tag;
    string internal key = "SELECT_SPOOF_SEEN";

    function setTag(bytes32 _tag) external {
        tag = _tag;
    }

    function setKey(string calldata _key) external {
        key = _key;
    }

    function swap() external {
        if (!vm.envOr(key, false)) {
            vm.setEnv(key, "true");
            bytes memory b = abi.encodeWithSelector(Measured.selector, uint256(1e30), tag);
            assembly ("memory-safe") {
                revert(add(b, 0x20), mload(b))
            }
        }
    }
}

contract TestToken is IERC20 {
    string public constant name = "T";
    string public constant symbol = "T";
    uint8 public constant decimals = 18;
    uint256 public totalSupply;
    mapping(address => uint256) public balanceOf;
    mapping(address => mapping(address => uint256)) public allowance;

    function mint(address to, uint256 a) external {
        balanceOf[to] += a;
        totalSupply += a;
    }

    function transfer(address to, uint256 a) external returns (bool) {
        balanceOf[msg.sender] -= a;
        balanceOf[to] += a;
        return true;
    }

    function transferFrom(address f, address to, uint256 a) external returns (bool) {
        if (allowance[f][msg.sender] != type(uint256).max) allowance[f][msg.sender] -= a;
        balanceOf[f] -= a;
        balanceOf[to] += a;
        return true;
    }

    function approve(address s, uint256 a) external returns (bool) {
        allowance[msg.sender][s] = a;
        return true;
    }
}

/// @notice Controllable leg: delivers `amt` buy token to the caller and bumps `callCount`
///         (disposable frames roll it back); `doRevert` fails after delivering.
contract Pool {
    IERC20 internal immutable t;
    uint256 internal amt;
    bool internal doRevert;
    uint256 public callCount;

    constructor(IERC20 _t) {
        t = _t;
    }

    function set(uint256 _amt, bool _doRevert) external {
        amt = _amt;
        doRevert = _doRevert;
    }

    function swap() external {
        callCount++;
        t.transfer(msg.sender, amt);
        if (doRevert) revert("leg reverted");
    }
}

/// @notice A pathological leg: burns all gas forwarded to it, then OOG-reverts.
contract GasBurnerPool {
    function swap() external pure {
        while (true) {
            assembly ("memory-safe") {
                pop(keccak256(0x00, 0x20))
            }
        }
    }
}

/// @notice A finisher that needs more than the per-candidate cap, but less than the uncapped
///         final-attempt budget after earlier capped stalls.
contract GasHeavyPool {
    IERC20 internal immutable t;
    uint256 internal amt;
    uint256 internal burnIterations;
    uint256 public callCount;

    constructor(IERC20 _t) {
        t = _t;
    }

    function set(uint256 _amt, uint256 _burnIterations) external {
        amt = _amt;
        burnIterations = _burnIterations;
    }

    function swap() external {
        callCount++;
        for (uint256 i; i < burnIterations; i++) {
            assembly ("memory-safe") {
                pop(keccak256(0x00, 0x20))
            }
        }
        t.transfer(msg.sender, amt);
    }
}

/// @notice SELECT_VIP leg: pulls the VIP-funded sell token from Settler, then sends buy token back
///         to Settler for balance-delta scoring.
contract SelectVIPSellPool {
    Vm internal constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    IERC20 internal immutable sell;
    IERC20 internal immutable buy;
    uint256 internal buyAmount;
    bool internal doRevert;
    string internal key;

    constructor(IERC20 _sell, IERC20 _buy) {
        sell = _sell;
        buy = _buy;
    }

    function set(uint256 _buyAmount, bool _doRevert) external {
        buyAmount = _buyAmount;
        doRevert = _doRevert;
    }

    function setKey(string calldata _key) external {
        key = _key;
    }

    function swap(uint256 sellAmount) external {
        if (bytes(key).length != 0) vm.setEnv(key, "true");
        sell.transferFrom(msg.sender, address(this), sellAmount);
        buy.transfer(msg.sender, buyAmount);
        if (doRevert) revert("vip leg reverted");
    }
}

/// @notice Fakes a high measurement once, then under-delivers on commit so SELECT_VIP must drop it
///         and commit the real runner-up with the same Permit2 nonce.
contract SelectVIPSpoofPool {
    Vm internal constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    bytes32 internal tag;
    string internal key = "SELECT_VIP_SPOOF_SEEN";

    function setTag(bytes32 _tag) external {
        tag = _tag;
    }

    function swap(uint256) external {
        if (!vm.envOr(key, false)) {
            vm.setEnv(key, "true");
            bytes memory b = abi.encodeWithSelector(Measured.selector, uint256(1e30), tag);
            assembly ("memory-safe") {
                revert(add(b, 0x20), mload(b))
            }
        }
    }
}
