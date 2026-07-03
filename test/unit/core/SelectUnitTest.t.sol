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

/// @notice Exercises the real `BaseSettler` `SELECT` action (scalar v1): fallback (CASCADE, no
///         measure), descending ladder (CASCADE, per-rung targets), best-of-N (BEST) with the
///         fail-closed measured commit, the improvement fee, the win-outright 1x path, and the
///         candidate gas cap (a stalling candidate must not starve the rest). Only the AMM legs are
///         mocked (allowed for unit tests); the contract under test is the production Settler.
contract SelectUnitTest is Test {
    uint256 internal constant CASCADE = 0;
    uint256 internal constant BEST = 1;

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
            t := keccak256(add(e, 0x40), sub(mload(e), 0x20))
        }
    }

    function _candidates3() internal view returns (bytes[][] memory c) {
        c = new bytes[][](3);
        c[0] = _candidate(address(p0));
        c[1] = _candidate(address(p1));
        c[2] = _candidate(address(p2));
    }

    function _run(uint256 config, address token, uint256[] memory targets, bytes[][] memory candidates, uint256 minOut)
        internal
    {
        // tests pass a packed `config` (fold | shareBps<<8); unpack to the plain SELECT args
        uint256 fold = config & 0xff;
        uint256 shareBps = (config >> 8) & 0xffff;
        uint256[] memory hurdles = new uint256[](candidates.length);
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeWithSelector(
            ISettlerActions.SELECT.selector, fold, shareBps, uint256(0), token, targets, hurdles, candidates
        );
        vm.prank(taker, taker);
        settler.execute(
            ISettlerBase.AllowedSlippage({recipient: payable(recipient), buyToken: IERC20(address(buy)), minAmountOut: minOut}),
            actions,
            bytes32(0)
        );
    }

    /// @dev ROUTE_OR_FALLBACK personality: CASCADE with no measure (token = 0) and zero targets —
    ///      the failing primary is discarded wholesale, the alternate commits.
    function test_cascade_fallback() public {
        p0.set(10 ether, true); // delivers, then reverts
        p1.set(7 ether, false);
        _run(CASCADE, address(0), new uint256[](3), _candidates3(), 7 ether);
        assertEq(buy.balanceOf(recipient), 7 ether, "alternate's output only (primary rolled back)");
        assertEq(p1.callCount(), 1, "alternate committed");
        assertEq(p2.callCount(), 0, "third candidate never reached");
    }

    /// @dev Descending-floor LADDER personality: rung 0 misses its high floor, rung 1 clears its
    ///      lower floor and commits; rung 2 never runs.
    function test_cascade_ladder() public {
        p0.set(8 ether, false);
        p1.set(7 ether, false);
        p2.set(9 ether, false);
        uint256[] memory targets = new uint256[](3);
        targets[0] = 10 ether; // 8 < 10 -> Measured, walk down
        targets[1] = 6 ether; // 7 >= 6 -> commits
        targets[2] = 1;
        _run(CASCADE, address(buy), targets, _candidates3(), 7 ether);
        assertEq(buy.balanceOf(recipient), 7 ether, "rung 1 committed");
        assertEq(p2.callCount(), 0, "rung 2 never attempted");
    }

    /// @dev BEST: target missed, all candidates measured and rolled back, argmax committed at its
    ///      measured score (fail-closed).
    function test_best() public {
        p0.set(5 ether, false);
        p1.set(7 ether, false);
        p2.set(9 ether, false);
        uint256[] memory targets = new uint256[](3);
        targets[0] = 10 ether;
        _run(BEST, address(buy), targets, _candidates3(), 9 ether);
        assertEq(buy.balanceOf(recipient), 9 ether, "best (p2) committed");
        assertEq(p0.callCount() + p1.callCount(), 0, "losing measurements rolled back");
    }

    /// @dev The improvement fee: shareBps of (winner − runner-up), in the measured token. Winner 9,
    ///      runner-up 7 -> edge 2 -> 50% = 1 to the receiver, 8 to the recipient.
    function test_best_fee() public {
        p0.set(5 ether, false);
        p1.set(7 ether, false);
        p2.set(9 ether, false);
        uint256[] memory targets = new uint256[](3);
        targets[0] = 10 ether;
        _run(BEST | (5_000 << 8), address(buy), targets, _candidates3(), 8 ether);
        assertEq(buy.balanceOf(FEE_RECEIVER), 1 ether, "half the measured edge");
        assertEq(buy.balanceOf(recipient), 8 ether, "winner's output minus fee");
    }

    /// @dev Wins outright: 1x, nothing else measured, no fee.
    function test_best_winsOutright() public {
        p0.set(10 ether, false);
        uint256[] memory targets = new uint256[](3);
        targets[0] = 10 ether;
        _run(BEST | (5_000 << 8), address(buy), targets, _candidates3(), 10 ether);
        assertEq(buy.balanceOf(recipient), 10 ether);
        assertEq(p1.callCount() + p2.callCount(), 0, "nothing else measured");
        assertEq(buy.balanceOf(FEE_RECEIVER), 0, "no fee on the outright win");
    }

    /// @dev The tag is computable from public calldata, so an adversarial pool CAN forge
    ///      `Measured(huge, correctTag)` to win selection, then under-deliver on the commit
    ///      (measurements roll back all EVM state, so in production only gas introspection
    ///      distinguishes measure from commit; here a forge env var stands in). The commit re-runs
    ///      at the measured score, so the under-delivery reverts `Measured(0, tag)` — fail-closed —
    ///      instead of settling a bad fill.
    function test_best_spoofCorrectTag_failsClosed() public {
        vm.setEnv("SELECT_SPOOF_SEEN", "false");
        p0.set(8 ether, false);
        p2.set(0, false);
        DiscriminatingSpoofPool evil = new DiscriminatingSpoofPool();
        bytes[] memory evilCandidate = _candidate(address(evil));
        bytes32 tag = _tag(evilCandidate);
        evil.setTag(tag);
        uint256[] memory targets = new uint256[](3);
        targets[0] = 20 ether; // candidate 0 misses -> full runoff
        bytes[][] memory candidates = new bytes[][](3);
        candidates[0] = _candidate(address(p0));
        candidates[1] = evilCandidate;
        candidates[2] = _candidate(address(p2));
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeWithSelector(
            ISettlerActions.SELECT.selector, BEST, uint256(0), uint256(0), address(buy), targets, new uint256[](3), candidates
        );
        vm.prank(taker, taker);
        vm.expectRevert(abi.encodeWithSelector(Measured.selector, uint256(0), tag));
        settler.execute(
            ISettlerBase.AllowedSlippage({recipient: payable(recipient), buyToken: IERC20(address(0)), minAmountOut: 0}),
            actions,
            bytes32(0)
        );
        assertEq(buy.balanceOf(recipient), 0, "nothing settled");
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
    function test_cascade_gasCap_stallingCandidateCannotStarve() public {
        p1.set(7 ether, false);
        bytes[][] memory candidates = new bytes[][](2);
        candidates[0] = _candidate(address(new GasBurnerPool()));
        candidates[1] = _candidate(address(p1));
        uint256[] memory targets = new uint256[](2);
        bytes[] memory actions = new bytes[](1);
        actions[0] = abi.encodeWithSelector(
            ISettlerActions.SELECT.selector, CASCADE, uint256(0), uint256(300_000), address(0), targets, new uint256[](2), candidates
        );
        vm.prank(taker, taker);
        settler.execute{gas: 1_500_000}(
            ISettlerBase.AllowedSlippage({recipient: payable(recipient), buyToken: IERC20(address(buy)), minAmountOut: 7 ether}),
            actions,
            bytes32(0)
        );
        assertEq(buy.balanceOf(recipient), 7 ether, "alternate committed despite the staller");
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

    function setTag(bytes32 _tag) external {
        tag = _tag;
    }

    function swap() external {
        if (!vm.envOr("SELECT_SPOOF_SEEN", false)) {
            vm.setEnv("SELECT_SPOOF_SEEN", "true");
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
