// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Test} from "@forge-std/Test.sol";
import {Vm} from "@forge-std/Vm.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";

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
    BaseSettler internal settler;
    TestToken internal buy;
    Pool internal p0;
    Pool internal p1;
    Pool internal p2;
    address internal recipient = makeAddr("recipient");
    address internal taker = makeAddr("taker");

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

    function _candidates3() internal view returns (bytes[][] memory c) {
        c = new bytes[][](3);
        c[0] = _candidate(address(p0));
        c[1] = _candidate(address(p1));
        c[2] = _candidate(address(p2));
    }

    function _bestOfTargets(uint256 belief) internal pure returns (uint256[] memory targets) {
        targets = _unreachableTargets(3);
        targets[0] = belief;
    }

    function _run(address token, uint256[] memory targets, bytes[][] memory candidates, uint256 minOut) internal {
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(ISettlerActions.SELECT, (uint256(0), token, targets, candidates));
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

    function test_measured_bestOfN_commitsArgmax() public {
        p0.set(5 ether, false);
        p1.set(7 ether, false);
        p2.set(9 ether, false);
        uint256[] memory targets = _bestOfTargets(10 ether);
        _run(address(buy), targets, _candidates3(), 9 ether);
        assertEq(buy.balanceOf(recipient), 9 ether, "best (p2) committed");
        assertEq(p0.callCount() + p1.callCount(), 0, "losing measurements rolled back");
    }

    function test_measured_bestOfN_treatsScoresAsUnsigned() public {
        uint256 highScore = 1 << 255;
        buy.mint(address(p0), highScore);
        p0.set(highScore, false);
        p1.set(1 ether, false);
        uint256[] memory targets = _bestOfTargets(type(uint256).max);

        _run(address(buy), targets, _candidates3(), highScore);

        assertEq(buy.balanceOf(recipient), highScore, "uint256 argmax committed");
    }

    function test_measured_winsOutright_skipsMeasurements() public {
        p0.set(10 ether, false);
        uint256[] memory targets = _bestOfTargets(10 ether);
        _run(address(buy), targets, _candidates3(), 10 ether);
        assertEq(buy.balanceOf(recipient), 10 ether);
        assertEq(p1.callCount() + p2.callCount(), 0, "nothing else measured");
    }

    function test_measured_spoofCorrectTag_degradesToRunnerUp() public {
        vm.setEnv("SELECT_SPOOF_SEEN", "false");
        p0.set(8 ether, false);
        p2.set(0, false);
        SpoofPool evil = new SpoofPool("SELECT_SPOOF_SEEN");
        bytes[] memory evilCandidate = _candidate(address(evil));
        bytes32 tag = _tag(evilCandidate);
        evil.setTag(tag);
        uint256[] memory targets = _bestOfTargets(20 ether);
        bytes[][] memory candidates = new bytes[][](3);
        candidates[0] = _candidate(address(p0));
        candidates[1] = evilCandidate;
        candidates[2] = _candidate(address(p2));
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(ISettlerActions.SELECT, (uint256(0), address(buy), targets, candidates));
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

    function test_measured_allCommitPhaseCommitsFail_bubblesLastRevert() public {
        vm.setEnv("SELECT_SPOOF_SEEN_0", "false");
        vm.setEnv("SELECT_SPOOF_SEEN_1", "false");
        SpoofPool evil0 = new SpoofPool("SELECT_SPOOF_SEEN_0");
        bytes[] memory evilCandidate0 = _candidate(address(evil0));
        evil0.setTag(_tag(evilCandidate0));
        SpoofPool evil1 = new SpoofPool("SELECT_SPOOF_SEEN_1");
        bytes[] memory evilCandidate1 = _candidate(address(evil1));
        bytes32 tag1 = _tag(evilCandidate1);
        evil1.setTag(tag1);
        uint256[] memory targets = _unreachableTargets(2);
        bytes[][] memory candidates = new bytes[][](2);
        candidates[0] = evilCandidate0;
        candidates[1] = evilCandidate1;
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(ISettlerActions.SELECT, (uint256(0), address(buy), targets, candidates));
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
        uint256[] memory targets = new uint256[](2);
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeCall(ISettlerActions.SELECT, (uint256(300_000), address(0), targets, candidates));
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
        _runWithGasCap(300_000, address(0), targets, candidates, 7 ether, 1_200_000);
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
        uint256[] memory targets = _unreachableTargets(4);
        _runWithGasCap(300_000, address(buy), targets, candidates, 8 ether, 1_150_000);
        assertEq(buy.balanceOf(recipient), 8 ether, "best measured-so-far committed");
        assertEq(p0.callCount(), 1, "measured best committed once");
        assertEq(p2.callCount(), 0, "unmeasured 9-token candidate skipped and excluded");
    }

    function test_measured_gasGuard_preservesCommitReserveForZeroScore() public {
        p0.set(0, false);
        bytes[][] memory candidates = new bytes[][](2);
        candidates[0] = _candidate(address(p0));
        candidates[1] = _candidate(address(new GasBurnerPool()));
        _runWithGasCap(300_000, address(buy), _unreachableTargets(2), candidates, 0, 750_000);
        assertEq(p0.callCount(), 1, "authenticated zero-score candidate committed");
    }
}

error ActionInvalid(uint256 i, bytes4 action, bytes data);

contract SpoofPool {
    Vm internal constant vm = Vm(address(uint160(uint256(keccak256("hevm cheat code")))));
    bytes32 internal tag;
    string internal key;

    constructor(string memory _key) {
        key = _key;
    }

    function setTag(bytes32 _tag) external {
        tag = _tag;
    }

    function swap() external {
        _spoof();
    }

    function swap(uint256) external {
        _spoof();
    }

    function _spoof() private {
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

contract GasBurnerPool {
    function swap() external pure {
        while (true) {
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
            assembly ("memory-safe") {
                pop(keccak256(0x00, 0x20))
            }
        }
        t.transfer(msg.sender, amt);
    }
}
