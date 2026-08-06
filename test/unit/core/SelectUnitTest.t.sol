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

abstract contract SelectShared {
    function _candidate(address p) internal pure returns (bytes[] memory c) {
        c = new bytes[](1);
        c[0] = abi.encodeCall(ISettlerActions.BASIC, (address(0), 0, p, 0, abi.encodeCall(Pool.swap, ())));
    }

    function _tag(bytes[] memory c) internal pure returns (bytes32 t) {
        bytes memory e = abi.encode(c);
        // Hash the candidate's ABI frame without copying it.
        // Equivalent Solidity: `t = keccak256(abi.encode(c)[32:])`.
        assembly ("memory-safe") {
            t := keccak256(add(e, 0x40), sub(mload(e), 0x20))
        }
    }

    function _unreachableTargets(uint256 n) internal pure returns (uint256[] memory targets) {
        targets = new uint256[](n);
        for (uint256 i; i < n; i++) {
            targets[i] = type(uint256).max;
        }
    }
}

contract SelectUnitTest is Test, SelectShared {
    address internal constant PERMIT2 = 0x000000000022D473030F116dDEE9F6B43aC78BA3;

    BaseSettler internal settler;
    MockPermit2 internal permit2 = MockPermit2(PERMIT2);
    TestToken internal sell;
    TestToken internal buy;
    Pool internal p0;
    Pool internal p1;
    Pool internal p2;
    address internal recipient = makeAddr("recipient");
    address internal taker = makeAddr("taker");
    address internal maker = makeAddr("maker");

    function setUp() public {
        vm.etch(PERMIT2, type(MockPermit2).runtimeCode);
        settler = new BaseSettler(bytes20(0));
        sell = new TestToken();
        buy = new TestToken();
        p0 = new Pool(buy);
        p1 = new Pool(buy);
        p2 = new Pool(buy);
        buy.mint(address(p0), 1_000 ether);
        buy.mint(address(p1), 1_000 ether);
        buy.mint(address(p2), 1_000 ether);
    }

    function _rfqCandidate(uint256 makerAmount, uint256 nonce) internal view returns (bytes[] memory c) {
        ISignatureTransfer.PermitTransferFrom memory permit = ISignatureTransfer.PermitTransferFrom({
            permitted: ISignatureTransfer.TokenPermissions({token: address(buy), amount: makerAmount}),
            nonce: nonce,
            deadline: type(uint256).max
        });
        c = new bytes[](1);
        c[0] = abi.encodeCall(
            ISettlerActions.RFQ, (address(settler), permit, maker, bytes(""), address(sell), uint256(1 ether))
        );
    }

    function _fundRfq(uint256 makerAmount) internal {
        sell.mint(address(settler), 1 ether);
        buy.mint(maker, makerAmount);
        vm.prank(maker);
        buy.approve(PERMIT2, type(uint256).max);
    }

    function _candidates3() internal view returns (bytes[][] memory c) {
        c = new bytes[][](3);
        c[0] = _candidate(address(p0));
        c[1] = _candidate(address(p1));
        c[2] = _candidate(address(p2));
    }

    function _firstReservation(uint256 target) internal pure returns (uint256[] memory targets) {
        targets = _unreachableTargets(3);
        targets[0] = target;
    }

    /// @dev A multi-candidate SELECT requires a nonzero cap so no trial can starve the fallback.
    uint256 internal constant TEST_GAS_CAP = 400_000;

    function _run(address token, uint256[] memory targets, bytes[][] memory candidates, uint256 minOut) internal {
        _runAction(_selectAction(TEST_GAS_CAP, token, targets, candidates), minOut);
    }

    function _selectAction(uint256 gasCap, address token, uint256[] memory targets, bytes[][] memory candidates)
        internal
        pure
        returns (bytes memory)
    {
        return abi.encodeCall(ISettlerActions.SELECT, (gasCap, token, targets, candidates));
    }

    function _runAction(bytes memory action, uint256 minOut) internal {
        bytes[] memory actions = new bytes[](1);
        actions[0] = action;
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
        uint256 gasCap,
        address token,
        uint256[] memory targets,
        bytes[][] memory candidates,
        uint256 minOut,
        uint256 txGas
    ) internal {
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(ISettlerActions.SELECT, (gasCap, token, targets, candidates));
        vm.prank(taker, taker);
        settler.execute{gas: txGas}(
            ISettlerBase.AllowedSlippage({
                recipient: payable(recipient), buyToken: IERC20(address(buy)), minAmountOut: minOut
            }),
            actions,
            bytes32(0)
        );
    }

    function test_bounds_candidateOffsetIntoTable_reverts() public {
        bytes[][] memory candidates = new bytes[][](1);
        candidates[0] = _candidate(address(p0));
        bytes memory action = _selectAction(TEST_GAS_CAP, address(0), new uint256[](1), candidates);
        // Point candidate 0 at its own offset-table entry instead of its encoded body.
        // Equivalent Solidity: `action.candidates[0].offset = 0`.
        assembly ("memory-safe") {
            let candidatesOffset := mload(add(action, 0x84))
            mstore(add(add(action, 0x44), candidatesOffset), 0x00)
        }

        vm.expectRevert();
        _runAction(action, 0);
    }

    function test_bounds_targetsRegionPastDataEnd_reverts() public {
        bytes[][] memory candidates = new bytes[][](1);
        candidates[0] = _candidate(address(p0));
        bytes memory action = _selectAction(TEST_GAS_CAP, address(0), new uint256[](1), candidates);
        // Point the targets array one word past the signed SELECT action.
        // Equivalent Solidity: `action.targets.offset = action.end + 32`.
        assembly ("memory-safe") {
            let actionEnd := add(add(action, 0x20), mload(action))
            let arguments := add(action, 0x24)
            mstore(add(action, 0x64), add(sub(actionEnd, arguments), 0x20))
        }

        vm.expectRevert();
        _runAction(action, 0);
    }

    function test_bounds_candidateOffsetBeforeCandidatesData_reverts() public {
        bytes[][] memory candidates = new bytes[][](1);
        candidates[0] = _candidate(address(p0));
        bytes memory action = _selectAction(TEST_GAS_CAP, address(0), new uint256[](1), candidates);
        // Move candidate 0 one word before the candidates offset table.
        // Equivalent Solidity: `action.candidates[0].offset = -32`.
        assembly ("memory-safe") {
            let candidatesOffset := mload(add(action, 0x84))
            mstore(add(add(action, 0x44), candidatesOffset), not(0x1f))
        }

        vm.expectRevert();
        _runAction(action, 0);
    }

    function test_bounds_candidateOffsetPastDataEnd_reverts() public {
        bytes[][] memory candidates = new bytes[][](1);
        candidates[0] = _candidate(address(p0));
        bytes memory action = _selectAction(TEST_GAS_CAP, address(0), new uint256[](1), candidates);
        // Point candidate 0 one word past the signed SELECT action.
        // Equivalent Solidity: `action.candidates[0].start = action.end + 32`.
        assembly ("memory-safe") {
            let candidatesOffset := mload(add(action, 0x84))
            let candidatesData := add(add(action, 0x44), candidatesOffset)
            let actionEnd := add(add(action, 0x20), mload(action))
            mstore(candidatesData, add(sub(actionEnd, candidatesData), 0x20))
        }

        vm.expectRevert();
        _runAction(action, 0);
    }

    function test_bounds_decreasingCandidateOffsets_reverts() public {
        bytes[][] memory candidates = new bytes[][](2);
        candidates[0] = _candidate(address(p0));
        candidates[1] = _candidate(address(p1));
        bytes memory action = _selectAction(TEST_GAS_CAP, address(0), new uint256[](2), candidates);
        // Reverse the two candidate-frame starts.
        // Equivalent Solidity: `(offset[0], offset[1]) = (offset[1], offset[0])`.
        assembly ("memory-safe") {
            let candidatesOffset := mload(add(action, 0x84))
            let candidatesData := add(add(action, 0x44), candidatesOffset)
            let first := mload(candidatesData)
            let second := mload(add(candidatesData, 0x20))
            mstore(candidatesData, second)
            mstore(add(candidatesData, 0x20), first)
        }

        vm.expectRevert();
        _runAction(action, 0);
    }

    function test_bounds_overlappingCandidateOffsets_reverts() public {
        bytes[][] memory candidates = new bytes[][](2);
        candidates[0] = _candidate(address(p0));
        candidates[1] = _candidate(address(p1));
        bytes memory action = _selectAction(TEST_GAS_CAP, address(0), new uint256[](2), candidates);
        // Give both candidates the same frame start.
        // Equivalent Solidity: `offset[1] = offset[0]`.
        assembly ("memory-safe") {
            let candidatesOffset := mload(add(action, 0x84))
            let candidatesData := add(add(action, 0x44), candidatesOffset)
            mstore(add(candidatesData, 0x20), mload(candidatesData))
        }

        vm.expectRevert();
        _runAction(action, 0);
    }

    function test_bounds_candidateFrameOverlapsTargets_reverts() public {
        bytes[][] memory candidates = new bytes[][](1);
        candidates[0] = _candidate(address(p0));
        bytes memory action = _selectAction(TEST_GAS_CAP, address(0), new uint256[](1), candidates);
        // Point candidate 0 at the targets data word.
        // Equivalent Solidity: `candidateStart = targetsData`.
        assembly ("memory-safe") {
            let targetsOffset := mload(add(action, 0x64))
            let candidatesOffset := mload(add(action, 0x84))
            let targetsData := add(add(action, 0x44), targetsOffset)
            let candidatesData := add(add(action, 0x44), candidatesOffset)
            mstore(candidatesData, sub(targetsData, candidatesData))
        }

        vm.expectRevert();
        _runAction(action, 0);
    }

    function test_bounds_trailingBytesAfterLastCandidate_reverts() public {
        bytes[][] memory candidates = new bytes[][](1);
        candidates[0] = _candidate(address(p0));
        bytes memory action =
            bytes.concat(_selectAction(TEST_GAS_CAP, address(0), new uint256[](1), candidates), abi.encode(bytes32(0)));

        vm.expectRevert();
        _runAction(action, 0);
    }

    function test_bounds_zeroCandidates_reverts() public {
        vm.expectRevert();
        _run(address(0), new uint256[](0), new bytes[][](0), 0);
    }

    function test_bounds_fourCandidates_reverts() public {
        bytes[][] memory candidates = new bytes[][](4);
        candidates[0] = _candidate(address(p0));
        candidates[1] = _candidate(address(p1));
        candidates[2] = _candidate(address(p2));
        candidates[3] = _candidate(address(p0));

        vm.expectRevert();
        _run(address(0), new uint256[](4), candidates, 0);
    }

    function test_bounds_threeCandidates_passes() public {
        p2.set(7 ether, false);
        uint256[] memory targets = _unreachableTargets(3);
        targets[2] = 7 ether;

        _run(address(buy), targets, _candidates3(), 7 ether);

        assertEq(buy.balanceOf(recipient), 7 ether);
    }

    function test_fallback_primaryRevert_commitsAlternate() public {
        p0.set(10 ether, true);
        p1.set(7 ether, false);
        _run(address(0), new uint256[](3), _candidates3(), 7 ether);
        assertEq(buy.balanceOf(recipient), 7 ether, "alternate's output only (primary rolled back)");
        assertEq(p1.callCount(), 1, "alternate committed");
        assertEq(p2.callCount(), 0, "third candidate never reached");
    }

    function test_ladder_firstReachableTargetCommits() public {
        p0.set(8 ether, false);
        p1.set(7 ether, false);
        p2.set(9 ether, false);
        uint256[] memory targets = new uint256[](3);
        targets[0] = 10 ether;
        targets[1] = 6 ether;
        targets[2] = 1;
        _run(address(buy), targets, _candidates3(), 7 ether);
        assertEq(buy.balanceOf(recipient), 7 ether, "rung 1 committed");
        assertEq(p2.callCount(), 0, "rung 2 never attempted");
    }

    function test_allReservationsMiss_revertsLastMeasurement() public {
        p0.set(5 ether, false);
        p1.set(7 ether, false);
        p2.set(9 ether, false);
        bytes[][] memory candidates = _candidates3();

        vm.expectRevert(abi.encodeWithSelector(Measured.selector, 9 ether, _tag(candidates[2])));
        _run(address(buy), _unreachableTargets(3), candidates, 0);
    }

    function test_firstCandidateClearsReservation_skipsRest() public {
        p0.set(10 ether, false);
        uint256[] memory targets = _firstReservation(10 ether);
        _run(address(buy), targets, _candidates3(), 10 ether);
        assertEq(buy.balanceOf(recipient), 10 ether);
        assertEq(p1.callCount() + p2.callCount(), 0, "later candidates not attempted");
    }

    function test_allCandidatesFail_bubblesLastReturndata() public {
        p0.set(0, true);
        RevertingPool last = new RevertingPool("last candidate");
        bytes[][] memory candidates = new bytes[][](2);
        candidates[0] = _candidate(address(p0));
        candidates[1] = _candidate(address(last));

        vm.expectRevert("last candidate");
        _run(address(0), new uint256[](2), candidates, 0);
    }

    function test_losingRfq_rollsBackMakerPermitAndTransfers() public {
        uint256 nonce = 42;
        _fundRfq(7 ether);
        p0.set(9 ether, false);
        bytes[][] memory candidates = new bytes[][](2);
        candidates[0] = _rfqCandidate(7 ether, nonce);
        candidates[1] = _candidate(address(p0));
        uint256[] memory targets = _unreachableTargets(2);
        targets[1] = 9 ether;

        _run(address(buy), targets, candidates, 9 ether);

        assertEq(buy.balanceOf(recipient), 9 ether, "non-RFQ winner committed");
        assertFalse(permit2.nonceUsed(maker, nonce), "losing maker permit rolled back");
        assertEq(buy.balanceOf(maker), 7 ether, "losing maker transfer rolled back");
        assertEq(sell.balanceOf(maker), 0, "losing taker transfer rolled back");
    }

    function test_winningRfq_consumesMakerPermitOnce() public {
        uint256 nonce = 43;
        _fundRfq(9 ether);
        p0.set(7 ether, false);
        bytes[][] memory candidates = new bytes[][](2);
        candidates[0] = _rfqCandidate(9 ether, nonce);
        candidates[1] = _candidate(address(p0));
        uint256[] memory targets = _unreachableTargets(2);
        targets[0] = 9 ether;

        _run(address(buy), targets, candidates, 9 ether);

        assertEq(buy.balanceOf(recipient), 9 ether, "RFQ winner committed");
        assertTrue(permit2.nonceUsed(maker, nonce), "winning maker permit persisted");
        assertEq(buy.balanceOf(maker), 0, "maker paid the committed output");
        assertEq(sell.balanceOf(maker), 1 ether, "maker received the committed input");
    }

    function testFuzz_shortNestedAction_revertsCleanly(uint256 len) public {
        len = bound(len, 0, 3);
        bytes[] memory actions = new bytes[](1);
        actions[0] = new bytes(len);
        vm.prank(address(settler));
        vm.expectPartialRevert(ActionInvalid.selector);
        Select(address(settler)).executeSelected(actions, IERC20(address(0)), 0, bytes32(0));
    }

    function test_fallback_gasCap_stallingCandidateCannotStarve() public {
        p1.set(7 ether, false);
        bytes[][] memory candidates = new bytes[][](2);
        candidates[0] = _candidate(address(new GasBurnerPool()));
        candidates[1] = _candidate(address(p1));
        _runWithGasCap(300_000, address(0), new uint256[](2), candidates, 7 ether, 1_500_000);
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
        _runWithGasCap(300_000, address(0), new uint256[](3), candidates, 7 ether, 1_200_000);
        assertEq(buy.balanceOf(recipient), 7 ether, "final fallback candidate committed");
        assertEq(finisher.callCount(), 1, "final candidate ran uncapped");
    }

    function test_fallback_zeroGasCapWithMultipleCandidates_reverts() public {
        p0.set(7 ether, false);
        bytes[][] memory candidates = new bytes[][](2);
        candidates[0] = _candidate(address(p0));
        candidates[1] = _candidate(address(p1));

        vm.expectRevert();
        _runWithGasCap(0, address(0), new uint256[](2), candidates, 0, 1_000_000);

        assertEq(p0.callCount(), 0, "first candidate not attempted without a cap");
    }

    function test_gasCap_insufficientReserve_revertsBeforeFirstCandidate() public {
        p0.set(8 ether, false);
        p1.set(7 ether, false);
        bytes[][] memory candidates = new bytes[][](2);
        candidates[0] = _candidate(address(p0));
        candidates[1] = _candidate(address(p1));

        vm.expectRevert();
        _runWithGasCap(300_000, address(0), new uint256[](2), candidates, 0, 500_000);

        assertEq(p0.callCount(), 0, "first candidate not attempted without reserve");
        assertEq(p1.callCount(), 0, "second candidate not attempted without reserve");
    }

    function _commitLogs() internal returns (Vm.Log[] memory out) {
        Vm.Log[] memory logs = vm.getRecordedLogs();
        out = new Vm.Log[](logs.length);
        uint256 n;
        for (uint256 i; i < logs.length; i++) {
            if (logs[i].emitter == address(settler) && logs[i].topics.length == 1) {
                out[n++] = logs[i];
            }
        }
        // Shrink the filtered memory array in place without copying it.
        // Equivalent Solidity: return an array containing only `out[0:n]`.
        assembly ("memory-safe") {
            mstore(out, n)
        }
    }

    function test_log_firstCommit_emitsWinnerTagAndScoreOnce() public {
        p0.set(10 ether, false);
        bytes[][] memory candidates = _candidates3();
        vm.recordLogs();
        _run(address(buy), new uint256[](3), candidates, 10 ether);
        Vm.Log[] memory logs = _commitLogs();
        assertEq(logs.length, 1, "exactly one commit log");
        assertEq(logs[0].topics[0], _tag(candidates[0]), "topic is candidate 0's tag");
        assertEq(abi.decode(logs[0].data, (uint256)), 10 ether, "data is the committed score");
    }

    function test_log_losingTrialEmitsNothing_commitTagOnly() public {
        p0.set(8 ether, false);
        p1.set(7 ether, false);
        bytes[][] memory candidates = _candidates3();
        uint256[] memory targets = new uint256[](3);
        targets[0] = 10 ether;
        targets[1] = 6 ether;
        targets[2] = 1;
        vm.recordLogs();
        _run(address(buy), targets, candidates, 7 ether);
        Vm.Log[] memory logs = _commitLogs();
        assertEq(logs.length, 1, "losing trial emitted nothing");
        assertEq(logs[0].topics[0], _tag(candidates[1]), "topic is the committed candidate's tag");
        assertEq(abi.decode(logs[0].data, (uint256)), 7 ether, "data is the committed score");
    }

    function test_log_allCandidatesFail_noLog() public {
        p0.set(0, true);
        p1.set(0, true);
        p2.set(0, true);
        vm.recordLogs();
        vm.expectRevert("leg reverted");
        _run(address(buy), new uint256[](3), _candidates3(), 0);
        assertEq(_commitLogs().length, 0, "no commit, no log");
    }
}

error ActionInvalid(uint256 i, bytes4 action, bytes data);

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

contract MockPermit2 {
    mapping(address owner => mapping(uint256 nonce => bool used)) public nonceUsed;

    function permitWitnessTransferFrom(
        ISignatureTransfer.PermitTransferFrom calldata permit,
        ISignatureTransfer.SignatureTransferDetails calldata transferDetails,
        address owner,
        bytes32,
        string calldata,
        bytes calldata
    ) external {
        require(!nonceUsed[owner][permit.nonce], "nonce used");
        nonceUsed[owner][permit.nonce] = true;
        IERC20(permit.permitted.token).transferFrom(owner, transferDetails.to, transferDetails.requestedAmount);
    }
}

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

contract RevertingPool {
    string internal reason;

    constructor(string memory _reason) {
        reason = _reason;
    }

    function swap() external view {
        revert(reason);
    }
}

contract GasBurnerPool {
    function swap() external pure {
        while (true) {
            // Consume gas without memory growth.
            // Equivalent Solidity: repeatedly hash one zeroed word.
            assembly ("memory-safe") {
                pop(keccak256(0x00, 0x20))
            }
        }
    }
}

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
            // Burn a predictable amount of gas without growing memory.
            // Equivalent Solidity: hash one zeroed word on every iteration.
            assembly ("memory-safe") {
                pop(keccak256(0x00, 0x20))
            }
        }
        t.transfer(msg.sender, amt);
    }
}
