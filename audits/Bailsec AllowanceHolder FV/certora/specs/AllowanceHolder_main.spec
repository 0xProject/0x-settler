import "./base/allowanceHolder_main.spec";

// HL-01: After exec, slot for (operator, sender, token) equals exactly amount
rule execSetsAllowanceExactly(env e) {
    //input variables
    address operator;
    address token;
    uint256 amount;
    address target;
    require(target == CallbackTarget, "Target must be MockCallbackTarget");
    bytes data;
    require(e.msg.sender != AllowanceHolderHarness, "Sender must not be AllowanceHolder");
    require(e.msg.sender == e.tx.origin, "Sender must be the original sender to prevent setting the allowance to 0");

    //function call
    AllowanceHolderHarness.execHarness(e, operator, token, amount, target, data);

    uint256 allowanceAfter = allowance[ghostEphemeralSlot(operator, e.msg.sender, token)];

    assert(allowanceAfter == amount, "Allowance should be exactly the amount");
}

// HL-02: exec with amount == 0 sets the ephemeral allowance to 0 and still executes the target call.
rule execWithZeroAmountSetsZeroAllowance(env e) {
    //input variables
    address operator;
    address token;
    uint256 amount = 0;
    address target = CallbackTarget;
    bytes data;
    address owner = e.msg.sender;
    require(owner != AllowanceHolderHarness, "Owner must be different from AllowanceHolder");

    //values before the function call
    uint256 beforeAllowance = allowance[ghostEphemeralSlot(operator, owner, token)];
    require(beforeAllowance != 0, "Allowance must be different from 0");

    //function call
    AllowanceHolderHarness.execHarness(e, operator, token, amount, target, data);

    //values after the function call
    uint256 afterAllowance = allowance[ghostEphemeralSlot(operator, owner, token)];

    //assert that the allowance has been set to 0
    assert(afterAllowance == 0, "Allowance is set to 0");
}

// HL-03: Only the operator can consume its allowance
rule onlyRegisteredOperatorConsumesAllowance(env e){
    //input variables
    address operator;
    address otherOperator;
    require(otherOperator != operator, "Other operator must be different from operator");
    address owner;
    address token;
    address recipient;
    uint256 amount;
    require(amount > 0, "Amount must be greater than 0");

    //values before the function call
    uint256 allowanceBefore = allowance[ghostEphemeralSlot(operator, owner, token)];
    uint256 otherAllowanceBefore = allowance[ghostEphemeralSlot(otherOperator, owner, token)];

    //function call
    AllowanceHolderHarness.transferFromHarness(e, token, owner, recipient, amount);

    //values after the function call
    uint256 allowanceAfter = allowance[ghostEphemeralSlot(operator, owner, token)];
    uint256 otherAllowanceAfter = allowance[ghostEphemeralSlot(otherOperator, owner, token)];

    //if the msg.sender = operator the allowance is reduced and the other operator allowance is not changed
    assert(e.msg.sender == operator => allowanceAfter == allowanceBefore - amount && otherAllowanceAfter == otherAllowanceBefore,
                    "If the msg.sender = operator the allowance is reduced and the other operator allowance is not changed");
}

// HL-07: A successful transferFrom moves exactly amount of token from owner to recipient
rule transferFromMovesExactlyAmount(env e) {
    //input variables
    address token;
    address owner;
    address recipient;
    uint256 amount;

    require(owner != recipient, "Owner and recipient should not be the same");

    //other variables
    address operator = e.msg.sender;

    //values before the function call
    mathint balanceBeforeOwner = ghostBalances[token][owner];
    mathint balanceBeforeRecipient = ghostBalances[token][recipient];

    //function call
    AllowanceHolderHarness.transferFromHarness(e, token, owner, recipient, amount);

    //values after the function call
    mathint balanceAfterOwner = ghostBalances[token][owner];
    mathint balanceAfterRecipient = ghostBalances[token][recipient];

    //assert that the tokens were transferred from owner to recipient
    assert(balanceAfterOwner == balanceBeforeOwner - amount, "Owner balance should have decreased");
    assert(balanceAfterRecipient == balanceBeforeRecipient + amount, "Recipient balance should have increased");
}

// HL-04 - Operator isolation in callback.
rule integratedNonOperatorCannotConsumeGrant(env e) {
    address operator;
    address token;
    uint256 amount;
    address target;
    bytes data;
    uint256 a1;
    uint256 a2;

    require(target == DoubleCallbackTarget, "target must be DoubleCallbackTarget");
    require(operator != DoubleCallbackTarget, "operator must not be DoubleCallbackTarget");   // the callback caller is NOT the operator
    require(!ghostIsERC20[target], "target must not be ERC20");
    require(e.msg.sender != AllowanceHolderHarness, "msg.sender must not be AllowanceHolder");
    require(e.msg.sender == e.tx.origin, "msg.sender must be the original sender");
    require(e.msg.value == 0, "msg.value must be 0");

    require(Config.token() == token, "token must be the same");
    require(Config.owner() == e.msg.sender, "owner must be the same");
    require(Config.amount1() == a1, "amount1 must be the same");
    require(Config.amount2() == a2, "amount2 must be the same");

    AllowanceHolderHarness.execHarness@withrevert(e, operator, token, amount, target, data);
    bool reverted = lastReverted;

    uint256 grantAfter = allowance[ghostEphemeralSlot(operator, e.msg.sender, token)];

    // exec set the operator's grant to `amount`; the non-operator callbacks key a
    // different slot, so whenever exec completes the operator's grant is untouched.
    assert !reverted => grantAfter == amount,
        "callbacks from a non-operator target cannot consume the operator's grant";
}

// HL-05 - on a successful target call, exec does not revert and returns the target's exact returndata (length 32, word 0xbeef).
rule execReturnsTargetReturndata(env e) {
    address operator;
    address token;
    uint256 amount;
    address target;
    bytes data;

    require (target == ConstReturnTarget, "target must be ConstReturnTarget");
    require (!ghostIsERC20[target], "target not ERC20 => only reverts in target are considered");
    require (e.msg.value == 0, "msg.value must be 0 => prevent exec itself to revert");

    uint256 word;
    uint256 len;
    word, len = AllowanceHolderHarness.execReturnWordAndLengthHarness@withrevert(e, operator, token, amount, target, data);

    assert !lastReverted, "exec must not revert when the target call succeeds";
    assert len == 32, "exec must return exactly the target's returndatasize (one word)";
    assert word == 0xbeef, "exec must return the target's returndata word";
}

// HL-06 - Cumulative consumed <= granted.
rule integratedConsumptionWithinGrant(env e) {
    address operator;
    address token;
    uint256 amount;
    address target;
    bytes data;
    uint256 a1;
    uint256 a2;

    require(operator == DoubleCallbackTarget, "operator must be DoubleCallbackTarget");
    require(target == DoubleCallbackTarget, "target must be DoubleCallbackTarget");
    require(!ghostIsERC20[target], "target must not be ERC20");
    require(e.msg.sender != AllowanceHolderHarness, "msg.sender must not be AllowanceHolder");
    require(e.msg.sender == e.tx.origin, "msg.sender must be the original sender");
    require(e.msg.value == 0, "msg.value must be 0");

    require(Config.token() == token, "token must be the same");
    require(Config.owner() == e.msg.sender, "owner must be the same");
    require(Config.amount1() == a1, "amount1 must be the same");
    require(Config.amount2() == a2, "amount2 must be the same");

    // exec succeeds (no @withrevert): we reason about completed integrated flows
    AllowanceHolderHarness.execHarness(e, operator, token, amount, target, data);

    uint256 grantAfter = allowance[ghostEphemeralSlot(operator, e.msg.sender, token)];

    assert to_mathint(grantAfter) == to_mathint(amount) - to_mathint(a1) - to_mathint(a2),
        "grant slot must equal granted amount minus the two consumed amounts";
    assert to_mathint(a1) + to_mathint(a2) <= to_mathint(amount),
        "cumulative consumption across the two callbacks cannot exceed the granted amount";
}

// HL-08 - Recipient inflow <= granted.
rule integratedRecipientInflowWithinGrant(env e) {
    address operator;
    address token;
    uint256 amount;
    address target;
    bytes data;
    address recipient;
    uint256 a1;
    uint256 a2;

    require(operator == DoubleCallbackTarget, "operator must be DoubleCallbackTarget");
    require(target == DoubleCallbackTarget, "target must be DoubleCallbackTarget");
    require(!ghostIsERC20[target], "target must not be ERC20");
    require(e.msg.sender != AllowanceHolderHarness, "msg.sender must not be AllowanceHolder");
    require(e.msg.sender == e.tx.origin, "msg.sender must be the original sender");
    require(e.msg.value == 0, "msg.value must be 0");

    require(Config.token() == token, "token must be the same");
    require(Config.owner() == e.msg.sender, "owner must be the same");
    require(Config.recipient() == recipient, "recipient must be the same");
    require(Config.amount1() == a1, "amount1 must be the same");
    require(Config.amount2() == a2, "amount2 must be the same");

    // distinct owner/recipient so the balance delta is purely the inflow
    require recipient != e.msg.sender;

    mathint recipientBefore = ghostBalances[token][recipient];

    AllowanceHolderHarness.execHarness(e, operator, token, amount, target, data);

    mathint recipientAfter = ghostBalances[token][recipient];

    assert recipientAfter - recipientBefore <= to_mathint(amount),
        "recipient cannot receive more than the granted amount during the exec flow";
}

// HL-09 - Full amount is consumable (liveness).
rule integratedFullAmountConsumable(env e) {
    address operator;
    address token;
    uint256 amount;
    address target;
    bytes data;
    address recipient;
    uint256 a1;
    uint256 a2;

    require(operator == DoubleCallbackTarget, "operator must be DoubleCallbackTarget");
    require(target == DoubleCallbackTarget, "target must be DoubleCallbackTarget");
    require(!ghostIsERC20[target], "target must not be ERC20");
    require(e.msg.sender != AllowanceHolderHarness, "msg.sender must not be AllowanceHolder");
    require(e.msg.sender == e.tx.origin, "msg.sender must be the original sender");
    require(e.msg.value == 0, "msg.value must be 0");

    require(Config.token() == token, "token must be the same");
    require(Config.owner() == e.msg.sender, "owner must be the same");
    require(Config.recipient() == recipient, "recipient must be the same");
    require(Config.amount1() == a1, "amount1 must be the same");
    require(Config.amount2() == a2, "amount2 must be the same");

    // both callbacks consume a positive amount and together draw the full grant
    require(a1 > 0, "amount1 must be greater than 0");
    require(a2 > 0, "amount2 must be greater than 0");
    require(to_mathint(a1) + to_mathint(a2) == to_mathint(amount), "amount1 + amount2 must be equal to amount");

    // owner funded for both moves; distinct recipient
    require(recipient != e.msg.sender, "recipient must not be the same as the msg.sender");
    require(ghostBalances[token][e.msg.sender] >= to_mathint(amount), "balance must be greater than or equal to amount");

    AllowanceHolderHarness.execHarness@withrevert(e, operator, token, amount, target, data);

    satisfy !lastReverted, "operator can draw the full granted amount across two callbacks";
}

// ST-01: exec(): Resets the ephemeral allowance to zero after execution whenever the resolved sender differs from tx origin
rule nonEoaSenderAllowanceReset(env e) {
    //input variables
    address operator;
    address token;
    uint256 amount;
    address target;
    require(target == CallbackTarget, "Target must be  MockCallbackTarget");
    bytes data;
    address owner = cvlMsgSender(e);
    require(owner != e.tx.origin, "Sender must not be the original sender");

    //function call
    AllowanceHolderHarness.execHarness(e, operator, token, amount, target, data);

    uint256 allowanceAfter = allowance[ghostEphemeralSlot(operator, owner, token)];

    assert(allowanceAfter == 0, "Allowance should be 0");
}

// UT-01: Uses 0xdead when data.length <= 0x10 or extracted target <= 0xffff (precompile range)
rule rejectIfERC20FallbackTargetsCorrectAddress(env e) {
    //input variables
    address maybeERC20;
    bytes data;

    require(!ghostIsERC20[maybeERC20], "Force non-reverting path to avoid vacuity");
    require(e.msg.value == 0, "Value must be 0 because function is view");

    //compute the target the same way _rejectIfERC20Inner does
    address target = AllowanceHolderHarness.rejectIfERC20Harness(e, maybeERC20, data);

    // Reference: the harness's pure re-implementation of the same logic
    address expected = AllowanceHolderHarness.computeRejectTarget(data);

    // Case 1: short data — can't extract an address, defaults to 0xdead
    assert(data.length <= 0x10 => target == 0xdead,
        "Short data (<=0x10 bytes) must resolve to 0xdead");

    // Case 2: target is never a precompile — either 0xdead or > 0xffff
    assert(to_mathint(target) > 0xffff || target == 0xdead,
        "Target passed to checkCall must never be in precompile range");

    // Case 3: actual target matches the unmutated reference computation
    assert(target == expected,
        "Target must match reference implementation computeRejectTarget");
}

// UT-02: _rejectIfERC20(): Reverts with ConfusedDeputy when the target behaves as an ERC20 token
rule rejectIfERC20RevertsForERC20Target(env e){
    //input variables
    address target;
    bytes data;

    //values before the function call
    bool isERC20 = ghostIsERC20[target];
    require(isERC20 == true, "Target must be an ERC20");
    require(e.msg.value == 0, "Value must be 0 because function is not payable");

    //function call
    AllowanceHolderHarness.rejectIfERC20Harness@withrevert(e, target, data);
    bool reverted = lastReverted;

    //assert that the call reverted
    assert(lastReverted, "RejectIfERC20 function did not revert but should have");
}

// UT-03 - exec reverts when its target call reverts (control-flow propagation only, not the revert bytes)
rule execPropagatesTargetRevert(env e) {
    address operator;
    address token;
    uint256 amount;
    address target;

    require (target == RevertTarget, "target must be RevertTarget"); // RevertTarget.triggerRevert() always reverts
    require (!ghostIsERC20[target], "target must not be ERC20 => prevetn exec itself to revert");

    //function call
    RevertCaller.callExecToRevertTarget@withrevert(e, operator, token, amount, target);

    assert lastReverted, "exec must revert when the target call reverts";
}

// UT-04: Slot written by exec is keyed on validated _msgSender, not raw msg.sender or operator
rule allowanceKeyedOnForwardedSender(env e) {
    //input variables
    address operator;
    address token;
    uint256 amount;
    address target;
    require(target == CallbackTarget, "Target must be inert MockCallbackTarget to avoid recursive dispatch and callback consumption");
    bytes data;
    require(data.length >= 20, "Data must be at least 20 bytes");

    require(e.msg.sender != AllowanceHolderHarness => e.msg.sender == e.tx.origin);
    require(e.msg.sender == AllowanceHolderHarness => ghostForwardedSender == e.tx.origin);

    //function call
    AllowanceHolderHarness.execHarness(e, operator, token, amount, target, data);

    //check that allowance is keyed on the effective sender
    uint256 allowanceAfterMsgSender = allowance[ghostEphemeralSlot(operator, e.msg.sender, token)];
    uint256 allowanceAfterForwarded = allowance[ghostEphemeralSlot(operator, ghostForwardedSender, token)];

    assert(e.msg.sender != AllowanceHolderHarness => allowanceAfterMsgSender == amount, "Non-self-call: allowance is keyed on msg.sender");
    assert(e.msg.sender == AllowanceHolderHarness => allowanceAfterForwarded == amount, "Self-call: allowance is keyed on the forwarded sender");
}

// UT-05 - exec forwards exactly msg.value to the target
rule execForwardsMsgValueToTarget(env e) {
    address operator;
    address token;
    uint256 amount;
    address target;
    bytes data;

    require target == ValueTarget, "target must be ValueTarget";
    require (!ghostIsERC20[target], "target not ERC20 => only reverts in target are considered");
    require (e.msg.sender != AllowanceHolderHarness, "msg.sender != AllowanceHolder => changes in nativeBalances can be observed");
    require (e.msg.sender != target, "msg.sender != target => delta nativeBalance is purely the inflow");

    //values before
    mathint nativeBalanceBefore = nativeBalances[target];

    //function call
    AllowanceHolderHarness.execReturnHarness(e, operator, token, amount, target, data);

    //values after
    mathint nativeBalanceAfter = nativeBalances[target];

    assert(nativeBalanceAfter == nativeBalanceBefore + to_mathint(e.msg.value),
        "exec must forward exactly msg.value to the target");
}

// UT-06: _rejectIfERC20 does NOT revert when target is not an ERC20
rule rejectIfERC20PassesOnNonERC20Target(env e) {
    //input variables
    address target;
    bytes data;

    //values before the function call
    bool isERC20 = ghostIsERC20[target];
    require(isERC20 == false, "Target must not be an ERC20");
    require(e.msg.value == 0, "Value must be 0 becasue function is not payable");

    //function call
    AllowanceHolderHarness.rejectIfERC20Harness@withrevert(e, target, data);

    //assert that the call did not revert
    assert(!lastReverted, "RejectIfERC20 function reverted but should not have");
}

// UT-07: exec(): Reverts when the target behaves as an ERC20 token
rule execRevertsForERC20Target(env e){
    //input variables
    address operator;
    address token;
    uint256 amount;
    address target;
    bytes data;

    //values before the function call
    bool isERC20 = ghostIsERC20[target];
    require(isERC20 == true, "Target must be an ERC20");
    require(e.msg.value == 0, "Value must be 0 because function is not payable");

    //function call
    AllowanceHolderHarness.execHarness@withrevert(e, operator, token, amount, target, data);
    bool reverted = lastReverted;

    //assert that the call reverted
    assert(lastReverted, "Exec must revert if the target is an ERC20");
}

// UT-08: transferFrom(): Reverts when amount exceeds the available ephemeral allowance
rule transferFromRevertsOnInsufficientAllowance(env e) {
    //input variables
    address token;
    address owner;
    address recipient;
    uint256 amount;

    //other variables
    address operator = e.msg.sender;
    uint256 allowanceBefore = allowance[ghostEphemeralSlot(operator, owner, token)];
    require(allowanceBefore < amount, "Amount must be bigger than allowance");

    //function call
    AllowanceHolderHarness.transferFromHarness@withrevert(e, token, owner, recipient, amount);

    uint256 allowanceAfter = allowance[ghostEphemeralSlot(operator, owner, token)];

    //assert that the call reverted
    assert(lastReverted, "TransferFrom function did not revert");
    assert(allowanceBefore == allowanceAfter, "Allowance should not have changed");
}

// UT-09: transferFrom(): Completes successfully without reverting when amount is zero
rule transferFromSucceedsOnZeroAmount(env e) {
    //input variables
    address token;
    address owner;
    address recipient;
    uint256 amount = 0;
    address operator = e.msg.sender;
    require(e.msg.value == 0, "Value must be 0 because function is not payable");

    //values before the function call
    uint256 beforeAllowance = allowance[ghostEphemeralSlot(operator, owner, token)];

    //function call
    AllowanceHolderHarness.transferFromHarness@withrevert(e, token, owner, recipient, amount);
    bool reverted = lastReverted;

    //values after the function call
    uint256 afterAllowance = allowance[ghostEphemeralSlot(operator, owner, token)];

    //assert that the allowance has not been modified
    assert(afterAllowance == beforeAllowance, "Allowance should not have been modified");
    assert(!reverted, "TransferFrom function should not have reverted");
}

// UT-10: transferFrom(): Decreases the operator's ephemeral allowance by exactly amount
rule transferFromDecrementsAllowanceByAmount(env e) {
    //input variables
    address token;
    address owner;
    address recipient;
    uint256 amount;

    //other variables
    address operator = e.msg.sender;

    //values before the function call
    uint256 allowanceBefore = allowance[ghostEphemeralSlot(operator, owner, token)];

    //function call
    AllowanceHolderHarness.transferFromHarness(e, token, owner, recipient, amount);

    //values after the function call
    uint256 allowanceAfter = allowance[ghostEphemeralSlot(operator, owner, token)];

    //assert that the transient allowance has been reduced by the amount
    assert(allowanceAfter == allowanceBefore - amount, "Transient allowance should have decreased");
}

// UT-11: _msgSender(): Returns msg sender when the caller is not the AllowanceHolder
rule msgSenderReturnsCallerWhenNotForwarded(env e) {
    //input variables
    bytes data;
    address sender = e.msg.sender;
    require(sender != currentContract, "Sender must not be self");

    //function call
    address result = AllowanceHolderHarness._msgSenderHarness(e,data);

    //assert that the result is the sender
    assert(result == sender, "Result must be the sender");
}

// UT-12: transferFrom does not affect ETH balance
rule noEtherRetainedAfterTransferFrom(env e) {
    address token; address owner; address recipient; uint256 amount;

    require(nativeBalances[AllowanceHolderHarness] == 0, "Starting balance must be 0");

    AllowanceHolderHarness.transferFromHarness@withrevert(e, token, owner, recipient, amount);

    assert(nativeBalances[AllowanceHolderHarness] == 0,
        "transferFrom must not change ETH balance");
}

// UT-13: exec with an inert target does not retain ETH
rule noEtherRetainedAfterExec(env e) {
    address operator; address token; uint256 amount; address target;
    bytes data;

    require(target == CallbackTarget, "Inert target to avoid DISPATCH-to-self loop");
    require(nativeBalances[AllowanceHolderHarness] == 0, "Starting balance must be 0");

    AllowanceHolderHarness.execHarness@withrevert(e, operator, token, amount, target, data);

    assert(nativeBalances[AllowanceHolderHarness] == 0,
        "exec with inert target must not retain ETH");
}

// UT-14: exec with an active callback target does not retain ETH
rule noEtherRetainedAfterExecWithCallback(env e) {
    address operator; address token; uint256 amount;
    address target;
    bytes data;

    require(target == ActiveCallbackTarget, "Active callback target");
    require(nativeBalances[AllowanceHolderHarness] == 0, "Starting balance must be 0");

    AllowanceHolderHarness.execHarness@withrevert(e, operator, token, amount, target, data);

    assert(nativeBalances[AllowanceHolderHarness] == 0,
        "exec with active callback must not retain ETH");
}

// VS-01: No persistent storage slot is ever written; all state lives in transient storage
rule noPersistentStorageWrites(method f, env e, calldataarg args ) {
    require(wrotePersistentStorage == false, "Persistent storage slot must not be written");

    //function call
    f(e, args);

    //assert that the persistent storage slot was not written
    assert(wrotePersistentStorage == false, "Persistent storage slot must not be written");
}

// VS-02: AllowanceHolder is either deployed to 0x0000000000001fF3684f28c67538d4D072C22734 or at block.chainid == 31337.
invariant deployedAtCorrectAddressOrLocalChain()
    currentContract == 0x0000000000001fF3684f28c67538d4D072C22734
    || AllowanceHolderHarness.deployChainId() == 31337;

// VT-01: transferFrom strictly decreases targeted allowance
rule transferFromOnlyDecreases(env e){
    //input variables
    address token;
    address owner;
    address recipient;
    uint256 amount;
    address operator = e.msg.sender;

    //values before
    uint256 allowanceBefore = allowance[ghostEphemeralSlot(operator, owner, token)];

    //function call
    transferFromHarness(e, token, owner, recipient, amount);

    //values after
    uint256 allowanceAfter = allowance[ghostEphemeralSlot(operator, owner, token)];

    assert(allowanceAfter <= allowanceBefore, "transferFrom only decreases the allowance");
}

// VT-02: Allowance slot changes only via exec (set), transferFrom (decrement)
rule allowanceSlotChangesOnlyViaExecOrTransferFrom(method f, env e, calldataarg args) {
    //input variables
    address token;
    address owner;
    address operator;

    uint256 beforeAllowance = allowance[ghostEphemeralSlot(operator, owner, token)];
    f(e, args);
    uint256 afterAllowance = allowance[ghostEphemeralSlot(operator, owner, token)];

    assert(afterAllowance != beforeAllowance =>
        f.selector == sig:AllowanceHolderHarness.execHarness(address,address,uint256,address,bytes).selector
        || f.selector == sig:AllowanceHolderHarness.transferFromHarness(address,address,address,uint256).selector
        || f.selector == sig:AllowanceHolderHarness.execReturnHarness(address,address,uint256,address,bytes).selector
        || f.selector == sig:AllowanceHolderHarness.execReturnWordAndLengthHarness(address,address,uint256,address,bytes).selector
        || f.isFallback,
        "Allowance should only be changed by specific functions");

}

