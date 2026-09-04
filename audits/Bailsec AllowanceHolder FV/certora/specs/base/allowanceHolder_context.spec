using AllowanceHolderHarness as AllowanceHolderHarness;
using MockContextContract as ContextContract;
using MockCallerContract as CallerContract;
using MockReturnSizeTarget as ReturnSizeTarget;

methods {
    function _.balanceOf(address owner) external => DISPATCH [
        MockContextContract._,
        MockReturnSizeTarget.balanceOf(address)
    ] default HAVOC_ECF;

    unresolved external in _._ => DISPATCH(use_fallback=true) [
        MockContextContract._,
        MockActiveCallbackTarget._,
        MockReturnSizeTarget.balanceOf(address),
        AllowanceHolderHarness.selExecHarness(),
        AllowanceHolderHarness.selTransferFromHarness(),
        AllowanceHolderHarness.selBalanceOfHarness()
    ] default HAVOC_ECF;
}


