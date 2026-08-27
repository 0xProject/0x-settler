import "./base/allowanceHolder_msgSender.spec";

// UT-24 - self-call _msgSender() returns the last 20 bytes of msg.data.
rule msgSenderReturnsLast20BytesOfMsgDataOnSelfCall(env e) {
    bytes data;

    // ERC-2771 forwarding appends a 20-byte sender; require a >=20-byte tail so the
    // tail slice is well-defined (msg.data.length - 20 does not underflow).
    require(data.length >= 20, "msg.data must be at least 20 bytes to avoid underflow");

    // Self-call branch: msg.sender == address(this) so _msgSender() takes the
    // `_msgSenderSol()` path. (The non-self path is covered by UT-11.)
    require(e.msg.sender == AllowanceHolderHarness, "trigger the self-call branch");

    address fromMsgSender;
    address fromTail;
    fromMsgSender, fromTail = AllowanceHolderHarness.msgSenderVsTailHarness(e, data);

    assert fromMsgSender == fromTail,
        "self-call _msgSender() must return the last 20 bytes of this frame's msg.data";
}
