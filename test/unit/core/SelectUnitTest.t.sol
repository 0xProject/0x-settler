// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {Vm} from "@forge-std/Vm.sol";
import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";
import {MockERC20} from "@solmate/test/utils/mocks/MockERC20.sol";
import {DeployPermit2} from "lib/permit2/test/utils/DeployPermit2.sol";

import {ISettlerActions} from "src/ISettlerActions.sol";
import {ISettlerBase} from "src/interfaces/ISettlerBase.sol";
import {BaseSettlerMetaTxn} from "src/chains/Base/MetaTxn.sol";
import {BaseSettler} from "src/chains/Base/TakerSubmitted.sol";
import {Shortfall} from "src/core/SettlerErrors.sol";
import {ActionDataBuilder} from "test/utils/ActionDataBuilder.sol";
import {Permit2Signature} from "test/utils/Permit2Signature.sol";

contract SelectUnitTest is Permit2Signature, DeployPermit2 {
    function _candidate(address p) internal pure returns (bytes[] memory c) {
        c = new bytes[](1);
        c[0] = abi.encodeCall(ISettlerActions.BASIC, (address(0), 0, p, 0, abi.encodeCall(Pool.swap, ())));
    }

    function _unreachableTargets(uint256 n) internal pure returns (uint256[] memory targets) {
        targets = new uint256[](n);
        for (uint256 i; i < n; i++) {
            targets[i] = type(uint256).max;
        }
    }

    uint256 internal constant MAKER_PRIVATE_KEY = 0x123456;
    uint256 internal constant METATXN_TAKER_PRIVATE_KEY = 0x654321;
    // The private callback tag: selector for `executeSelected(bytes[],address,uint256)`.
    bytes4 internal constant SELECT_CALLBACK_TAG = 0x1bbdbb47;
    bytes32 internal constant META_TXN_PERMIT2_WITNESS_TYPEHASH = keccak256(
        "PermitWitnessTransferFrom(TokenPermissions permitted,address spender,uint256 nonce,uint256 deadline,SlippageAndActions slippageAndActions)SlippageAndActions(address recipient,address buyToken,uint256 minAmountOut,bytes[] actions)TokenPermissions(address token,uint256 amount)"
    );
    bytes32 internal constant SLIPPAGE_AND_ACTIONS_TYPEHASH =
        keccak256("SlippageAndActions(address recipient,address buyToken,uint256 minAmountOut,bytes[] actions)");
    bytes32 internal constant RFQ_PERMIT2_WITNESS_TYPEHASH = keccak256(
        "PermitWitnessTransferFrom(TokenPermissions permitted,address spender,uint256 nonce,uint256 deadline,Consideration consideration)Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)TokenPermissions(address token,uint256 amount)"
    );
    bytes32 internal constant CONSIDERATION_TYPEHASH =
        keccak256("Consideration(address token,uint256 amount,address counterparty,bool partialFillAllowed)");

    BaseSettler internal settler;
    ISignatureTransfer internal constant permit2 = ISignatureTransfer(0x000000000022D473030F116dDEE9F6B43aC78BA3);
    MockERC20 internal sell;
    MockERC20 internal buy;
    Pool internal p0;
    Pool internal p1;
    Pool internal p2;
    address internal recipient = makeAddr("recipient");
    address internal taker = makeAddr("taker");
    address internal maker = vm.addr(MAKER_PRIVATE_KEY);

    function setUp() public {
        deployPermit2();
        settler = new BaseSettler(bytes20(0));
        sell = new MockERC20("Sell", "SELL", 18);
        buy = new MockERC20("Buy", "BUY", 18);
        p0 = new Pool(IERC20(address(buy)));
        p1 = new Pool(IERC20(address(buy)));
        p2 = new Pool(IERC20(address(buy)));
        buy.mint(address(p0), 1_000 ether);
        buy.mint(address(p1), 1_000 ether);
        buy.mint(address(p2), 1_000 ether);
    }

    function _rfqCandidate(uint256 makerAmount, uint256 nonce) internal view returns (bytes[] memory c) {
        ISignatureTransfer.PermitTransferFrom memory permit =
            defaultERC20PermitTransfer(address(buy), makerAmount, nonce);
        bytes32 witness = keccak256(abi.encode(CONSIDERATION_TYPEHASH, address(sell), 1 ether, taker, true));
        bytes memory makerSig = getPermitWitnessTransferSignature(
            permit,
            address(settler),
            MAKER_PRIVATE_KEY,
            RFQ_PERMIT2_WITNESS_TYPEHASH,
            witness,
            permit2.DOMAIN_SEPARATOR()
        );
        c = new bytes[](1);
        c[0] = abi.encodeCall(
            ISettlerActions.RFQ, (address(settler), permit, maker, makerSig, address(sell), uint256(1 ether))
        );
    }

    function _nonceUsed(address owner, uint256 nonce) internal view returns (bool) {
        uint256 mask = 1 << uint8(nonce);
        return permit2.nonceBitmap(owner, nonce >> 8) & mask != 0;
    }

    function _fundRfq(uint256 makerAmount) internal {
        sell.mint(address(settler), 1 ether);
        buy.mint(maker, makerAmount);
        vm.prank(maker);
        buy.approve(address(permit2), type(uint256).max);
    }

    function _gasBurner() internal returns (address) {
        return address(new GasHeavyPool(IERC20(address(buy)), 0, type(uint256).max));
    }

    function _candidates3() internal view returns (bytes[][] memory c) {
        c = new bytes[][](3);
        c[0] = _candidate(address(p0));
        c[1] = _candidate(address(p1));
        c[2] = _candidate(address(p2));
    }

    function _candidatePair(bytes[] memory first, bytes[] memory second)
        internal
        pure
        returns (bytes[][] memory candidates)
    {
        candidates = new bytes[][](2);
        candidates[0] = first;
        candidates[1] = second;
    }

    /// @dev A multi-candidate SELECT requires a nonzero cap so no trial can starve the fallback.
    uint256 internal constant TEST_GAS_CAP = 400_000;

    function _run(address token, uint256[] memory targets, bytes[][] memory candidates, uint256 minOut) internal {
        _runAction(_selectAction(TEST_GAS_CAP, token, targets, candidates), minOut);
    }

    function _unarmedCallbackCall() internal pure returns (bytes memory) {
        // An ABI-shaped callback payload: actions offset 0x60, zero token/minOut, empty actions array.
        return abi.encodeWithSelector(SELECT_CALLBACK_TAG, uint256(0x60), uint256(0), uint256(0), uint256(0));
    }

    function _selectAction(uint256 gasCap, address token, uint256[] memory targets, bytes[][] memory candidates)
        internal
        pure
        returns (bytes memory)
    {
        return abi.encodeCall(ISettlerActions.SELECT, (gasCap, token, targets, candidates));
    }

    function _runAction(bytes memory action, uint256 minOut) internal {
        _runAction(action, minOut, type(uint256).max);
    }

    function _runAction(bytes memory action, uint256 minOut, uint256 txGas) internal {
        vm.prank(taker, taker);
        settler.execute{gas: txGas}(
            ISettlerBase.AllowedSlippage({
                recipient: payable(recipient), buyToken: IERC20(address(buy)), minAmountOut: minOut
            }),
            ActionDataBuilder.build(action),
            bytes32(0)
        );
    }

    function test_ladder_fourCandidates_commitsFourth() public {
        p0.set(4 ether, false);
        p1.set(5 ether, false);
        p2.set(7 ether, false);
        bytes[][] memory candidates = new bytes[][](4);
        candidates[0] = _candidate(address(p0));
        candidates[1] = _candidate(address(p1));
        candidates[2] = _candidate(address(p2));
        candidates[3] = _candidate(address(p2));
        uint256[] memory targets = _unreachableTargets(4);
        targets[3] = 7 ether;

        _run(address(buy), targets, candidates, 7 ether);

        assertEq(buy.balanceOf(recipient), 7 ether);
        assertEq(p2.callCount(), 1, "only the committed fourth call persists");
    }

    function test_fallback_primaryRevert_commitsAlternate() public {
        p0.set(10 ether, true);
        p1.set(7 ether, false);
        _run(address(buy), new uint256[](3), _candidates3(), 7 ether);
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

    function test_allReservationsMiss_revertsLastShortfall() public {
        p0.set(5 ether, false);
        p1.set(7 ether, false);
        p2.set(9 ether, false);
        bytes[][] memory candidates = _candidates3();

        vm.expectRevert(abi.encodeWithSelector(Shortfall.selector, 9 ether));
        _run(address(buy), _unreachableTargets(3), candidates, 0);
    }

    function test_firstCandidateClearsReservation_skipsRest() public {
        p0.set(10 ether, false);
        uint256[] memory targets = _unreachableTargets(3);
        targets[0] = 10 ether;
        _run(address(buy), targets, _candidates3(), 10 ether);
        assertEq(buy.balanceOf(recipient), 10 ether);
        assertEq(p1.callCount() + p2.callCount(), 0, "later candidates not attempted");
    }

    function test_allCandidatesFail_bubblesLastReturndata() public {
        p0.set(0, false);
        p1.set(0, true);
        bytes[][] memory candidates = _candidatePair(_candidate(address(p0)), _candidate(address(p1)));
        uint256[] memory targets = new uint256[](2);
        targets[0] = 1;

        vm.expectRevert("leg reverted");
        _run(address(buy), targets, candidates, 0);
    }

    function test_losingRfq_rollsBackMakerPermitAndTransfers() public {
        uint256 nonce = 42;
        _fundRfq(7 ether);
        p0.set(9 ether, false);
        bytes[][] memory candidates = _candidatePair(_rfqCandidate(7 ether, nonce), _candidate(address(p0)));
        uint256[] memory targets = _unreachableTargets(2);
        targets[1] = 9 ether;

        _run(address(buy), targets, candidates, 9 ether);

        assertEq(buy.balanceOf(recipient), 9 ether, "non-RFQ winner committed");
        assertFalse(_nonceUsed(maker, nonce), "losing maker permit rolled back");
        assertEq(buy.balanceOf(maker), 7 ether, "losing maker transfer rolled back");
        assertEq(sell.balanceOf(maker), 0, "losing taker transfer rolled back");
    }

    function test_winningRfq_consumesMakerPermitOnce() public {
        uint256 nonce = 43;
        _fundRfq(9 ether);
        p0.set(7 ether, false);
        bytes[][] memory candidates = _candidatePair(_rfqCandidate(9 ether, nonce), _candidate(address(p0)));
        uint256[] memory targets = _unreachableTargets(2);
        targets[0] = 9 ether;

        _run(address(buy), targets, candidates, 9 ether);

        assertEq(buy.balanceOf(recipient), 9 ether, "RFQ winner committed");
        assertTrue(_nonceUsed(maker, nonce), "winning maker permit persisted");
        assertEq(buy.balanceOf(maker), 0, "maker paid the committed output");
        assertEq(sell.balanceOf(maker), 1 ether, "maker received the committed input");
    }

    function test_safety_failedTrial_clearsOperatorSlotForNextTrial() public {
        uint256 nonce = 45;
        _fundRfq(7 ether);
        p0.set(9 ether, false);

        bytes[][] memory innerCandidates = new bytes[][](1);
        innerCandidates[0] = _rfqCandidate(7 ether, nonce);
        uint256[] memory innerTargets = new uint256[](1);
        innerTargets[0] = 7 ether;

        bytes[] memory nestedCandidate =
            ActionDataBuilder.build(_selectAction(1, address(buy), innerTargets, innerCandidates));
        bytes[][] memory outerCandidates = _candidatePair(nestedCandidate, _candidate(address(p0)));
        uint256[] memory outerTargets = _unreachableTargets(2);
        outerTargets[1] = 9 ether;

        _run(address(buy), outerTargets, outerCandidates, 9 ether);

        assertFalse(_nonceUsed(maker, nonce), "nested losing permit rolled back");
        assertEq(buy.balanceOf(maker), 7 ether, "nested losing output rolled back");
        assertEq(sell.balanceOf(maker), 0, "nested losing input rolled back");
        assertEq(buy.balanceOf(recipient), 9 ether, "outer fallback committed");
    }

    function test_nestedSelect_finalFailureBubblesInnerShortfallIdentity() public {
        p0.set(5 ether, false);
        bytes[] memory innerCandidate = _candidate(address(p0));
        bytes[][] memory innerCandidates = new bytes[][](1);
        innerCandidates[0] = innerCandidate;
        bytes[] memory nestedCandidate =
            ActionDataBuilder.build(_selectAction(1, address(buy), _unreachableTargets(1), innerCandidates));
        bytes[][] memory outerCandidates = new bytes[][](1);
        outerCandidates[0] = nestedCandidate;

        vm.expectRevert(abi.encodeWithSelector(Shortfall.selector, 5 ether));
        _run(address(buy), _unreachableTargets(1), outerCandidates, 0);
    }

    function test_nestedSelect_uncappedOuterFallbackCanFundInnerReserve() public {
        p0.set(7 ether, false);
        bytes[][] memory innerCandidates = _candidatePair(_candidate(_gasBurner()), _candidate(address(p0)));
        uint256[] memory innerTargets = new uint256[](2);
        innerTargets[0] = 1;
        innerTargets[1] = 7 ether;
        bytes[] memory nestedCandidate =
            ActionDataBuilder.build(_selectAction(300_000, address(buy), innerTargets, innerCandidates));
        bytes[] memory emptyCandidate = new bytes[](0);
        bytes[][] memory outerCandidates = _candidatePair(nestedCandidate, emptyCandidate);
        uint256[] memory outerTargets = new uint256[](2);
        outerTargets[0] = 7 ether;
        uint256 before = vm.snapshotState();

        _runAction(_selectAction(300_000, address(buy), outerTargets, outerCandidates), 0, 2_000_000);

        assertEq(buy.balanceOf(recipient), 0, "empty outer fallback committed");
        assertEq(p0.callCount(), 0, "equal caps cannot fund the inner reserve");
        assertTrue(vm.revertToState(before));

        outerCandidates[0] = emptyCandidate;
        outerCandidates[1] = nestedCandidate;
        outerTargets[0] = 1;
        outerTargets[1] = 7 ether;
        _runAction(_selectAction(300_000, address(buy), outerTargets, outerCandidates), 7 ether, 2_000_000);

        assertEq(buy.balanceOf(recipient), 7 ether, "nested fallback committed");
        assertEq(p0.callCount(), 1, "inner fallback ran");
    }

    function test_metaTxn_signedSelect_executes() public {
        BaseSettlerMetaTxn metaTxn =
            BaseSettlerMetaTxn(payable(deployCode("MetaTxn.sol:BaseSettlerMetaTxn", abi.encode(bytes20(0)))));
        address metaTaker = vm.addr(METATXN_TAKER_PRIVATE_KEY);
        uint256 amount = 1 ether;
        uint256 nonce = 44;
        sell.mint(metaTaker, amount);
        vm.prank(metaTaker);
        sell.approve(address(permit2), type(uint256).max);

        ISignatureTransfer.PermitTransferFrom memory permit = defaultERC20PermitTransfer(address(sell), amount, nonce);
        bytes[][] memory candidates = new bytes[][](1);
        candidates[0] = new bytes[](0);
        bytes[] memory actions = ActionDataBuilder.build(
            abi.encodeCall(ISettlerActions.METATXN_TRANSFER_FROM, (address(metaTxn), permit)),
            _selectAction(1, address(sell), new uint256[](1), candidates)
        );

        ISettlerBase.AllowedSlippage memory slippage = ISettlerBase.AllowedSlippage({
            recipient: payable(metaTaker), buyToken: IERC20(address(sell)), minAmountOut: amount
        });
        bytes32 witness = keccak256(
            abi.encode(
                SLIPPAGE_AND_ACTIONS_TYPEHASH,
                slippage.recipient,
                slippage.buyToken,
                slippage.minAmountOut,
                keccak256(abi.encodePacked(keccak256(actions[0]), keccak256(actions[1])))
            )
        );
        bytes memory sig = getPermitWitnessTransferSignature(
            permit,
            address(metaTxn),
            METATXN_TAKER_PRIVATE_KEY,
            META_TXN_PERMIT2_WITNESS_TYPEHASH,
            witness,
            permit2.DOMAIN_SEPARATOR()
        );

        assertTrue(metaTxn.executeMetaTxn(slippage, actions, bytes32(0), metaTaker, sig));
        assertEq(sell.balanceOf(metaTaker), amount, "signed funds returned after SELECT");
        assertEq(sell.balanceOf(address(metaTxn)), 0, "SELECT left no custody");
        assertTrue(_nonceUsed(metaTaker, nonce), "signed Permit2 nonce consumed");
    }

    function testFuzz_shortNestedAction_revertsCleanly(uint256 len) public {
        len = bound(len, 0, 3);
        bytes[][] memory candidates = new bytes[][](1);
        candidates[0] = ActionDataBuilder.build(new bytes(len));
        vm.expectPartialRevert(ActionInvalid.selector);
        _run(address(buy), new uint256[](1), candidates, 0);
    }

    function test_safety_directExternalOldSelector_doesNothingDangerous() public {
        address caller = makeAddr("untrusted caller");

        vm.recordLogs();
        vm.prank(caller, caller);
        (bool success,) = address(settler).call(_unarmedCallbackCall());

        assertFalse(success, "unarmed selector rejected");
        assertEq(vm.getRecordedLogs().length, 0, "no logs");
    }

    function test_fallback_gasCap_stallingCandidateCannotStarve() public {
        p1.set(7 ether, false);
        bytes[][] memory candidates = _candidatePair(_candidate(_gasBurner()), _candidate(address(p1)));
        _runAction(_selectAction(300_000, address(buy), new uint256[](2), candidates), 7 ether, 1_500_000);
        assertEq(buy.balanceOf(recipient), 7 ether, "alternate committed despite the staller");
    }

    function test_fallback_gasCap_lastCandidateRunsUncapped() public {
        GasHeavyPool finisher = new GasHeavyPool(IERC20(address(buy)), 7 ether, 9_000);
        buy.mint(address(finisher), 7 ether);
        bytes[][] memory candidates = new bytes[][](3);
        candidates[0] = _candidate(_gasBurner());
        candidates[1] = _candidate(_gasBurner());
        candidates[2] = _candidate(address(finisher));
        _runAction(_selectAction(300_000, address(buy), new uint256[](3), candidates), 7 ether, 1_200_000);
        assertEq(buy.balanceOf(recipient), 7 ether, "final fallback candidate committed");
        assertEq(finisher.callCount(), 1, "final candidate ran uncapped");
    }

    function test_fallback_zeroGasCapWithMultipleCandidates_reverts() public {
        p0.set(7 ether, false);
        bytes[][] memory candidates = _candidatePair(_candidate(address(p0)), _candidate(address(p1)));

        vm.expectRevert();
        _runAction(_selectAction(1, address(buy), new uint256[](2), candidates), 0, 1_000_000);

        assertEq(p0.callCount(), 0, "first candidate not attempted without a cap");
    }

    function test_gasCap_insufficientReserve_revertsBeforeFirstCandidate() public {
        p0.set(8 ether, false);
        p1.set(7 ether, false);
        bytes[][] memory candidates = _candidatePair(_candidate(address(p0)), _candidate(address(p1)));

        vm.expectRevert();
        _runAction(_selectAction(300_000, address(buy), new uint256[](2), candidates), 0, 500_000);

        assertEq(p0.callCount(), 0, "first candidate not attempted without reserve");
        assertEq(p1.callCount(), 0, "second candidate not attempted without reserve");
    }

    function test_select_emitsNoSettlerLogs() public {
        p0.set(5 ether, false);
        p1.set(7 ether, false);
        bytes[][] memory candidates = _candidatePair(_candidate(address(p0)), _candidate(address(p1)));
        uint256[] memory targets = new uint256[](2);
        targets[0] = 6 ether;
        targets[1] = 7 ether;

        vm.recordLogs();
        _run(address(buy), targets, candidates, 7 ether);

        Vm.Log[] memory logs = vm.getRecordedLogs();
        for (uint256 i; i < logs.length; ++i) {
            assertTrue(logs[i].emitter != address(settler), "neither the miss nor the commit logs from Settler");
        }
        assertEq(buy.balanceOf(recipient), 7 ether, "second candidate committed");
    }

    function test_safety_basicSelfCallOldSelector_withoutArmedCallback_isInert() public {
        bytes memory action =
            abi.encodeCall(ISettlerActions.BASIC, (address(0), 0, address(settler), 0, _unarmedCallbackCall()));

        vm.recordLogs();
        vm.expectRevert();
        _runAction(action, 0);

        assertEq(vm.getRecordedLogs().length, 0, "no logs");
    }
}

error ActionInvalid(uint256 i, bytes4 action, bytes data);

/// @dev Separate contract: SelectUnitTest sits at the unit-profile deploy-gas ceiling.
contract SelectDecodeTest is Permit2Signature, DeployPermit2 {
    BaseSettler internal settler;
    MockERC20 internal buy;
    Pool internal p0;
    Pool internal p1;
    address internal recipient = makeAddr("recipient");
    address internal taker = makeAddr("taker");

    /// @dev A multi-candidate SELECT requires a nonzero cap so no trial can starve the fallback.
    uint256 internal constant TEST_GAS_CAP = 400_000;

    function setUp() public {
        deployPermit2();
        settler = new BaseSettler(bytes20(0));
        buy = new MockERC20("Buy", "BUY", 18);
        p0 = new Pool(IERC20(address(buy)));
        p1 = new Pool(IERC20(address(buy)));
        buy.mint(address(p0), 1_000 ether);
        buy.mint(address(p1), 1_000 ether);
    }

    function _candidate(address p) internal pure returns (bytes[] memory c) {
        c = new bytes[](1);
        c[0] = abi.encodeCall(ISettlerActions.BASIC, (address(0), 0, p, 0, abi.encodeCall(Pool.swap, ())));
    }

    function _unreachableTargets(uint256 n) internal pure returns (uint256[] memory targets) {
        targets = new uint256[](n);
        for (uint256 i; i < n; i++) {
            targets[i] = type(uint256).max;
        }
    }

    function _candidatePair(bytes[] memory first, bytes[] memory second)
        internal
        pure
        returns (bytes[][] memory candidates)
    {
        candidates = new bytes[][](2);
        candidates[0] = first;
        candidates[1] = second;
    }

    function _selectAction(uint256 gasCap, address token, uint256[] memory targets, bytes[][] memory candidates)
        internal
        pure
        returns (bytes memory)
    {
        return abi.encodeCall(ISettlerActions.SELECT, (gasCap, token, targets, candidates));
    }

    function _malformedAction(uint256 candidatesLength) internal view returns (bytes memory action) {
        bytes[][] memory candidates = new bytes[][](candidatesLength);
        for (uint256 i; i < candidatesLength; ++i) {
            candidates[i] = _candidate(address(p0));
        }
        action = _selectAction(TEST_GAS_CAP, address(buy), new uint256[](candidatesLength), candidates);
    }

    function _runAction(bytes memory action, uint256 minOut) internal {
        vm.prank(taker, taker);
        settler.execute(
            ISettlerBase.AllowedSlippage({
                recipient: payable(recipient), buyToken: IERC20(address(buy)), minAmountOut: minOut
            }),
            ActionDataBuilder.build(action),
            bytes32(0)
        );
    }

    function _runMalformed(bytes memory action) internal {
        vm.expectRevert();
        _runAction(action, 0);
    }

    function test_bounds_dirtyTokenUpperBits_reverts() public {
        bytes[][] memory candidates = new bytes[][](1);
        candidates[0] = _candidate(address(p0));
        bytes memory action = _selectAction(0, address(buy), new uint256[](1), candidates);
        // Dirty the most significant byte of the 160-bit `token` word (selector, gasCap, token).
        action[0x24] = 0x01;
        _runMalformed(action);
        assertEq(p0.callCount(), 0, "no trial ran on a dirty token");
    }

    function test_bounds_zeroToken_reverts() public {
        bytes[][] memory candidates = new bytes[][](1);
        candidates[0] = _candidate(address(p0));
        _runMalformed(_selectAction(0, address(0), new uint256[](1), candidates));
        assertEq(p0.callCount(), 0, "no trial ran on a zero token");
    }

    function test_bounds_candidateOffsetIntoTable_decodesAsEmpty() public {
        bytes memory action = _malformedAction(1);
        // Point candidate 0 at its own offset-table entry. Valid aliasing: the zero offset word
        // doubles as the candidate's length, so it decodes as no actions and commits against the
        // zero target.
        assembly ("memory-safe") {
            let candidatesOffset := mload(add(action, 0x84))
            mstore(add(add(action, 0x44), candidatesOffset), 0x00)
        }

        _runAction(action, 0);
        assertEq(p0.callCount(), 0, "empty-decoded candidate committed");
    }

    function test_bounds_unalignedGapBeforeDynamicTails_decodes() public {
        bytes memory action = _malformedAction(1);
        bytes memory gapped = new bytes(action.length + 0x01);
        // Solidity's ABI decoder follows unaligned offsets and permits a gap before the tails.
        assembly ("memory-safe") {
            let source := add(0x20, action)
            let destination := add(0x20, gapped)
            let headLength := 0x84
            mcopy(destination, source, headLength)
            mcopy(add(0x01, add(headLength, destination)), add(headLength, source), sub(mload(action), headLength))
            mstore(add(0x64, gapped), add(0x01, mload(add(0x64, action))))
            mstore(add(0x84, gapped), add(0x01, mload(add(0x84, action))))
        }

        _runAction(gapped, 0);
        assertEq(p0.callCount(), 1, "candidate after unaligned gap ran");
    }

    function test_bounds_aliasedDynamicTails_decode() public {
        // The word at 0x80 is both array lengths. The zero word at 0xa0 is
        // `targets[0]`, the candidate offset, and the empty candidate length.
        bytes memory action = abi.encodePacked(
            ISettlerActions.SELECT.selector,
            TEST_GAS_CAP,
            uint256(uint160(address(buy))),
            uint256(0x80),
            uint256(0x80),
            uint256(0x01),
            uint256(0x00)
        );

        _runAction(action, 0);
        assertEq(p0.callCount(), 0, "aliased empty candidate committed");
    }

    function test_bounds_candidateOffsetBeforeCandidatesData_reverts() public {
        bytes memory action = _malformedAction(1);
        // Move candidate 0 one word before the candidates offset table.
        // Equivalent Solidity: `action.candidates[0].offset = -32`.
        assembly ("memory-safe") {
            let candidatesOffset := mload(add(action, 0x84))
            mstore(add(add(action, 0x44), candidatesOffset), not(0x1f))
        }

        _runMalformed(action);
    }

    function test_bounds_candidateOffsetPastDataEnd_reverts() public {
        bytes memory action = _malformedAction(1);
        // Point candidate 0 one word past the signed SELECT action.
        // Equivalent Solidity: `action.candidates[0].start = action.end + 32`.
        assembly ("memory-safe") {
            let candidatesOffset := mload(add(action, 0x84))
            let candidatesData := add(add(action, 0x44), candidatesOffset)
            let actionEnd := add(add(action, 0x20), mload(action))
            mstore(candidatesData, add(sub(actionEnd, candidatesData), 0x20))
        }

        _runMalformed(action);
    }

    function test_bounds_decreasingCandidateOffsets_followPointersAfterMiss() public {
        bytes[][] memory candidates = _candidatePair(_candidate(address(p0)), _candidate(address(p1)));
        uint256[] memory targets = new uint256[](2);
        targets[0] = 1;
        bytes memory action = _selectAction(TEST_GAS_CAP, address(buy), targets, candidates);
        // Logical candidate 0 points to the physically later candidate. It misses before
        // logical candidate 1 points backward and commits.
        assembly ("memory-safe") {
            let candidatesOffset := mload(add(0x84, action))
            let candidatesData := add(candidatesOffset, add(0x44, action))
            let first := mload(candidatesData)
            let second := mload(add(0x20, candidatesData))
            mstore(candidatesData, second)
            mstore(add(0x20, candidatesData), first)
        }

        _runAction(action, 0);
        assertEq(p0.callCount(), 1, "lower physical candidate committed after miss");
        assertEq(p1.callCount(), 0, "missed candidate state reverted");
    }

    function test_bounds_equalCandidateOffsets_aliasCandidate() public {
        bytes memory action = _malformedAction(2);
        // Both logical candidates refer to the same encoded value.
        assembly ("memory-safe") {
            let candidatesOffset := mload(add(0x84, action))
            let candidatesData := add(candidatesOffset, add(0x44, action))
            mstore(add(0x20, candidatesData), mload(candidatesData))
        }

        _runAction(action, 0);
        assertEq(p0.callCount(), 1, "aliased first candidate ran");
    }

    function test_bounds_candidateOffsetWrapsBeforeBase_reverts() public {
        bytes memory action = _malformedAction(1);
        // Point candidate 0 at the targets data word.
        // Equivalent Solidity: `candidateStart = targetsData`.
        assembly ("memory-safe") {
            let targetsOffset := mload(add(action, 0x64))
            let candidatesOffset := mload(add(action, 0x84))
            let targetsData := add(add(action, 0x44), targetsOffset)
            let candidatesData := add(add(action, 0x44), candidatesOffset)
            mstore(candidatesData, sub(targetsData, candidatesData))
        }

        _runMalformed(action);
    }

    function test_trailingBytes_doNotChangeCandidate_trialStillRuns() public {
        bytes[][] memory candidates = new bytes[][](1);
        candidates[0] = _candidate(address(p0));
        // Unreferenced trailing bytes do not change the decoded value.
        bytes memory action = bytes.concat(
            _selectAction(TEST_GAS_CAP, address(buy), _unreachableTargets(1), candidates), abi.encode(bytes32(0))
        );

        vm.expectRevert(abi.encodeWithSelector(Shortfall.selector, 0));
        _runAction(action, 0);
    }

    function test_bounds_zeroCandidates_reverts() public {
        _runMalformed(_malformedAction(0));
    }

    function test_bounds_candidateCountMismatch_reverts() public {
        bytes memory action = _malformedAction(1);
        assembly ("memory-safe") {
            let dataStart := add(action, 0x24)
            let base := add(dataStart, mload(add(action, 0x84)))
            mstore(base, 0x02)
        }

        _runMalformed(action);
    }

    function test_bounds_aliasedDynamicTails_oversizedLengthReverts() public {
        bytes memory action = _malformedAction(1);
        // Alias both tails and make their shared length too large for the remaining data.
        assembly ("memory-safe") {
            mstore(add(action, 0x84), 0x80)
            mstore(add(action, 0xa4), not(0x00))
        }

        _runMalformed(action);
    }

    function test_bounds_outOfBoundsDynamicOffset_revertsBeforeTrial() public {
        bytes memory action = _malformedAction(1);
        assembly ("memory-safe") {
            mstore(add(0x64, action), not(0x00))
        }
        _runMalformed(action);
        assertEq(p0.callCount(), 0, "invalid dynamic offset ran no trial");
    }

    function test_bounds_gapBeforeFirstCandidate_executes() public {
        bytes memory action = _malformedAction(1);
        bytes memory gapped = new bytes(action.length + 0x01);
        // Splice one zero byte between the offset table and the candidate and update its offset.
        assembly ("memory-safe") {
            let candidatesOffset := mload(add(action, 0x84))
            let table0 := add(add(action, 0x44), candidatesOffset)
            let candidate := add(0x20, table0)
            let prefix := sub(candidate, add(action, 0x20))
            mcopy(add(gapped, 0x20), add(action, 0x20), prefix)
            mcopy(add(add(gapped, 0x21), prefix), candidate, sub(mload(action), prefix))
            mstore(add(add(gapped, 0x44), candidatesOffset), 0x21)
        }
        _runAction(gapped, 0);
        assertEq(p0.callCount(), 1, "gapped candidate executed unchanged");
    }

    function test_bounds_swappedTails_decodes() public {
        bytes[][] memory candidates = new bytes[][](1);
        candidates[0] = _candidate(address(p0));
        bytes memory candidatesTail = abi.encode(candidates);
        // Strip the outer offset word, leaving the bare length/table/candidate tail.
        assembly ("memory-safe") {
            let len := mload(candidatesTail)
            candidatesTail := add(0x20, candidatesTail)
            mstore(candidatesTail, sub(len, 0x20))
        }

        // A valid encoding with the candidates tail placed before the targets tail.
        bytes memory action = abi.encodePacked(
            ISettlerActions.SELECT.selector,
            TEST_GAS_CAP,
            uint256(uint160(address(buy))),
            0x80 + candidatesTail.length, // targetsOffset, after the candidates tail
            uint256(0x80), // candidatesOffset
            candidatesTail,
            uint256(1), // targets length
            uint256(0) // targets[0]
        );

        _runAction(action, 0);
        assertEq(p0.callCount(), 1, "swapped tails did not decode");
    }
}

/// @dev Separate contract: SelectUnitTest sits at the unit-profile deploy-gas ceiling.
contract SelectContainmentTest is Permit2Signature, DeployPermit2 {
    BaseSettler internal settler;
    MockERC20 internal buy;
    Pool internal p0;
    address internal recipient = makeAddr("recipient");
    address internal taker = makeAddr("taker");

    function setUp() public {
        deployPermit2();
        settler = new BaseSettler(bytes20(0));
        buy = new MockERC20("Buy", "BUY", 18);
        p0 = new Pool(IERC20(address(buy)));
        buy.mint(address(p0), 1_000 ether);
        p0.set(7 ether, false);
    }

    /// @dev One candidate, one authored action, with its inner action offset overwritten.
    function _perturbedAction(uint256 offset) internal view returns (bytes memory action) {
        bytes[][] memory candidates = new bytes[][](1);
        candidates[0] = new bytes[](1);
        candidates[0][0] =
            abi.encodeCall(ISettlerActions.BASIC, (address(0), 0, address(p0), 0, abi.encodeCall(Pool.swap, ())));
        action = abi.encodeCall(ISettlerActions.SELECT, (400_000, address(buy), new uint256[](1), candidates));
        assembly ("memory-safe") {
            let candidatesOffset := mload(add(action, 0x84))
            let candidate := add(add(action, 0x64), candidatesOffset)
            mstore(add(0x20, candidate), offset)
        }
    }

    function _execute(bytes memory action) internal {
        vm.prank(taker, taker);
        settler.execute(
            ISettlerBase.AllowedSlippage({
                recipient: payable(recipient), buyToken: IERC20(address(buy)), minAmountOut: 0
            }),
            ActionDataBuilder.build(action),
            bytes32(0)
        );
    }

    /// @dev The callback contains no bytes after the signed SELECT action data.
    function test_innerOffsetPastActionData_revertsActionInvalid() public {
        vm.expectPartialRevert(ActionInvalid.selector);
        _execute(_perturbedAction(0x2000));
    }

    /// @dev Any successful perturbation produces the authored payout; every failure leaves no residue.
    function testFuzz_innerOffsetPerturbation_staysInsideAction(uint256 offset) public {
        bytes memory action = _perturbedAction(offset);
        vm.prank(taker, taker);
        try settler.execute(
            ISettlerBase.AllowedSlippage({
                recipient: payable(recipient), buyToken: IERC20(address(buy)), minAmountOut: 0
            }),
            ActionDataBuilder.build(action),
            bytes32(0)
        ) {
            assertEq(buy.balanceOf(recipient), 7 ether, "a committing offset decoded the authored action");
        } catch {
            assertEq(buy.balanceOf(recipient), 0, "a failed trial paid nothing");
        }
        assertEq(buy.balanceOf(address(settler)), 0, "no residue either way");
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

contract GasHeavyPool {
    IERC20 internal immutable t;
    uint256 internal amt;
    uint256 internal burnIterations;
    uint256 public callCount;

    constructor(IERC20 _t, uint256 _amt, uint256 _burnIterations) {
        t = _t;
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
