using MockCallerContract as MockCaller;
using MockTransferFromReturnCaller as ReturnCaller;
use builtin rule sanity filtered { f -> f.contract == currentContract }

methods {
    //summarize functions
    function AllowanceHolder.exec(address, address, uint256, address, bytes calldata) internal returns (bytes memory) => CVLExecCalled() ALL;
    function AllowanceHolderBase.transferFrom(address, address, address, uint256) internal => CVLTransferFromCalled() ALL;

    // Dispatch the low-level call in MockCaller.callWithSelector into AllowanceHolder's fallback
    unresolved external in MockCallerContract.callWithSelector(uint32, bytes)
        => DISPATCH(use_fallback=true) [
            AllowanceHolderHarness._
        ] default NONDET;

    // Dispatch raw transferFrom calls into AllowanceHolder's fallback
    unresolved external in MockCallerContract.callTransferFromRawWithValue(uint256, uint256, uint256, uint256)
        => DISPATCH(use_fallback=true) [
            AllowanceHolderHarness._
        ] default NONDET;

    // Dispatch raw exec calls into AllowanceHolder's fallback
    unresolved external in MockCallerContract.callExecRaw(uint256, uint256, uint256, uint256, bytes)
        => DISPATCH(use_fallback=true) [
            AllowanceHolderHarness._
        ] default NONDET;

    unresolved external in MockTransferFromReturnCaller._
    => DISPATCH(use_fallback=true) [ AllowanceHolderHarness._ ] default NONDET;

}

function CVLExecCalled() returns bytes {
    ghostExecCalled = true;
    bytes empty;
    return empty;
}

function CVLTransferFromCalled() {
    ghostTransferFromCalled = true;
}

definition isHarnessHelperSelector(uint32 sel) returns bool =
    sel == 0x1bad3b4a // selExecHarness()
    || sel == 0x9fe0c597 // selTransferFromHarness()
    || sel == 0x37dde51a // selBalanceOfHarness()
    || sel == 0x0618ad35 // _msgSenderHarness(bytes)
    || sel == 0x881c35fc // execHarness(address,address,uint256,address,bytes)
    || sel == 0xebec1bf2 // transferFromHarness(address,address,address,uint256)
    || sel == 0x1d6ab3e4 // rejectIfERC20Harness(address,bytes)
    || sel == 0x98aba051 // callWithSelectorHarness(bytes4,bytes)
    || sel == 0x9b1762d9 // deployChainId()
    || sel == 0x0a78311d // computeRejectTarget(bytes)
    || sel == 0x8ca65a0f // msgSenderVsTailHarness(bytes)
    || sel == 0x3dc73267 // execReturnHarness(address,address,uint256,address,bytes)
    || sel == 0x75984294; // execReturnWordAndLengthHarness(address,address,uint256,address,bytes)

// tracks the original sender that called the AllowanceHolder contract
ghost bool ghostExecCalled;
ghost bool ghostTransferFromCalled;