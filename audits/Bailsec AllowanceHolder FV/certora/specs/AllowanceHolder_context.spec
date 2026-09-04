import "./base/allowanceHolder_context.spec";

//HL-10: For a exec call funneled through the AllowanceHolder, the the call is recognized as forwarded
rule callRecipientRecognizesCallAsForwarded(env e) {
    //input variables
    address operator;
    address token;
    uint256 amount;
    address target = ContextContract;
    bytes data;

    //function call
    CallerContract.callExecEndToEnd(e, operator, token, amount, target, data);

    //varibles after the call 
    bool isForwarded = ContextContract.savedIsForwarded(e);

    assert(isForwarded == true, "call is recognized as forwarded");
}

// HL-11: Any contract inheriting AllowanceHolderContext passes the "confused deputy" test
rule allowanceHolderContextPassesConfusedDeputyTest(env e) {
    //input variables
    address maybeERC20 = ContextContract;
    bytes data;

    require(e.msg.value == 0, "Value must be 0 because function is not payable");

    //function call
    rejectIfERC20Harness@withrevert(e, maybeERC20,data);
    bool reverted = lastReverted;

    //assert that the call reverted
    assert(!reverted, "RejectIfERC20 function should not have reverted");
}

//HL-12: For a exec call funneled through the AllowanceHolder, the callRecipient can extract the original sender from the call data
rule callRecipientCanExtractOriginalSenderFromCallData(env e) {
    //input variables
    address operator;
    address token;
    uint256 amount;
    address target = ContextContract;
    bytes data;
    
    //variables before the call
    // address msgSenderInContextContractBefore = ContextContract.savedMsgSender(e);

    //function call
    CallerContract.callExecEndToEnd(e, operator, token, amount, target, data);

    //varibles after the call
    address msgSenderInContextContractAfter = ContextContract.savedMsgSender(e);

    assert(msgSenderInContextContractAfter == CallerContract, "msgSenderInContextContract is the CallerContract");
}

// UT-30: _rejectIfERC20Inner(target, data) reverts with ConfusedDeputy IFF the
// target's balanceOf staticcall succeeds AND returns >= 32 bytes.
rule rejectIfERC20RevertsIffReturnAtLeast32Bytes(env e) {
    //input variables
    address maybeERC20 = ReturnSizeTarget;
    bytes data;

    //returndata-size and success of the target's balanceOf staticcall
    uint256 retLen;
    bool callSucceeds;

    require(e.msg.value == 0, "Value must be 0 because function is not payable");
    // Cover the 32-byte boundary: below, at, and above 32 (plus 0 / dust).
    require(retLen == 0 || retLen == 1 || retLen == 31 || retLen == 32 || retLen == 33,
        "retLen constrained to boundary values around 32");

    //configure the mock target's balanceOf returndata behaviour
    ReturnSizeTarget.setRetLen(e, retLen);
    ReturnSizeTarget.setCallSucceeds(e, callSucceeds);

    //function call
    rejectIfERC20Harness@withrevert(e, maybeERC20, data);
    bool reverted = lastReverted;

    //reverts (ConfusedDeputy) iff the balanceOf call succeeds and returns >= 32 bytes
    assert(reverted <=> (callSucceeds && retLen >= 32),
        "rejectIfERC20 reverts iff balanceOf succeeds and returns at least 32 bytes");
}

// UT-31: _isForwarded() returns true if the caller is the AllowanceHolder
rule isForwardedReturnsTrueIfCallerIsAllowanceHolder(env e) {
    //function call
    bool isForwarded = ContextContract.isForwardedHarness(e);

    assert(e.msg.sender == AllowanceHolderHarness => isForwarded == true, "Caller is the AllowanceHolder => call is forwarded");
    assert(e.msg.sender != AllowanceHolderHarness => isForwarded == false, "Caller is not the AllowanceHolder => call is not forwarded");
}

// UT-32: _msgSender(): if the caller is the ALLOWANCE_HOLDER, the last 20bytes of the data are returns as the actual msg.sender
rule strippedTailEqualsMsgSender(env e) {
    bytes extraData;
    address strippedTail;
    address msgSender;

    require(e.msg.sender == AllowanceHolderHarness, "Caller must be the AllowanceHolder");
    //function call
    (strippedTail, msgSender) = ContextContract.msgDataTailIsSenderHarness(e, extraData);

    assert(strippedTail == msgSender, "stripped tail equals msgSender");
}

//UT-33: _msgSender(): returns msg.sender if msg.sender is not the AllowanceHolder
rule msgSenderReturnsCallerWhenNotForwarded(env e) {
    bytes extraData;
    address sender = e.msg.sender;
    require(sender != AllowanceHolderHarness, "Sender must not be the AllowanceHolder");
    //function call
    address result = ContextContract.msgSenderHarness(e, extraData);
    assert(result == sender, "Result must be the sender");
}

// UT-34: _msgData strips 20 bytes from the data if msg.sender is the AllowanceHolder
rule msgDataStrips20BytesIfCallerIsAllowanceHolder(env e) {
    uint256 originalMsgDataLength;
    uint256 returnedMsgDataLength;
    bytes extraData;
    if(e.msg.sender == AllowanceHolderHarness) {
        require(extraData.length > 20, "extraData must be greater than 20");
    }
    require(e.msg.value == 0, "Value must be 0 because function is not payable");
    //function call
    (originalMsgDataLength, returnedMsgDataLength) = ContextContract.msgDataLengthHarness@withrevert(e, extraData);
    bool reverted = lastReverted;

    assert(!reverted, "msgDataLengthHarness does not revert");
    assert(e.msg.sender == AllowanceHolderHarness => originalMsgDataLength == returnedMsgDataLength - 20, "Caller is the AllowanceHolder => msgDataLength is 20 bytes less than rawMsgDataLength");
    assert(e.msg.sender != AllowanceHolderHarness => originalMsgDataLength == returnedMsgDataLength, "Caller is not the AllowanceHolder => msgDataLength is equal to rawMsgDataLength");
}

// UT-35: _msgData: returned data is not changed 
rule returnedMsgDataNotChanged(env e) {
    bytes1 originalMsgDataByte;
    bytes1 returnedMsgDataByte;
    uint256 index;
    bytes extraData;
    //function call
    (originalMsgDataByte, returnedMsgDataByte) = ContextContract.msgDataByteAtHarness(e, index, extraData);

    assert(originalMsgDataByte == returnedMsgDataByte, "returned msgData byte is not changed");
}



