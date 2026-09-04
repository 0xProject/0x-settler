import "../setup/TransientStorage.spec";
import "../setup/ERC20.spec";

using AllowanceHolderHarness as AllowanceHolderHarness;

// ALL-RULES mock targets
using MockCallbackTarget as CallbackTarget; 
using MockActiveCallbackTarget as ActiveCallbackTarget;

// exec-forwarding mock targets
using MockConstReturnTarget as ConstReturnTarget;   
using MockValueAcceptTarget as ValueTarget;         
using MockRevertTarget as RevertTarget;             
using MockExecRevertCaller as RevertCaller;         

// integrated-consumption mock targets
using MockDoubleCallbackTarget as DoubleCallbackTarget;  // re-enters transferFrom twice
using MockCallbackConfig as Config;                      // callback configuration getters

use builtin rule sanity;


methods {
    function AllowanceHolderHarness.deployChainId() external returns (uint256) envfree;
    function AllowanceHolderHarness.computeRejectTarget(bytes) external returns (address) envfree;
    function Config.amount1() external returns (uint256) envfree;
    function Config.amount2() external returns (uint256) envfree;
    function Config.token() external returns (address) envfree;
    function Config.owner() external returns (address) envfree;
    function Config.recipient() external returns (address) envfree;

    function TransientStorageLayout._ephemeralAllowance(address operator, address owner, address token) internal
        returns (TransientStorageBase.TSlot) => ghostEphemeralSlot(operator, owner, token);
    function _.checkCall(address target, bytes memory data, uint256 minReturnBytes) internal
        => CVLcheckCall(target, data) expect bool;

    unresolved external in _._ => DISPATCH(use_fallback=true) [
        MockCallbackTarget._,
        MockActiveCallbackTarget._,
        MockConstReturnTarget._,
        MockValueAcceptTarget._,
        MockRevertTarget._,
        MockDoubleCallbackTarget._
    ] default HAVOC_ECF;

    unresolved external in MockDoubleCallbackTarget._ => DISPATCH [
        MockCallbackConfig._,
        AllowanceHolderHarness._
    ] default NONDET;


    function AllowanceHolderBase._msgSenderSol() internal returns (address) => ghostForwardedSender;
}

function CVLcheckCall(address target, bytes data) returns (bool) {
    return ghostIsERC20[target];
}

function cvlMsgSender(env e) returns (address) {
    address caller = e.msg.sender; //current caller

    // Path 1: self-forwarded (via fallback -> _exec -> re-entry)
    if (caller == currentContract) {
        return ghostForwardedSender;
    }

    // Normal call: caller IS the sender
    return caller;
}

// Tracks whether AllowanceHolder itself executed a persistent SSTORE.
// `persistent` so it survives the havoc of the external call inside exec().
persistent ghost bool wrotePersistentStorage {
    init_state axiom !wrotePersistentStorage;
}

//tracks if a contract/target is an ERC20 or not
// target/contract => isERC20
ghost mapping(address => bool) ghostIsERC20;

// tracks the original sender that called the AllowanceHolder contract
ghost address ghostForwardedSender;

// tracks the target that was called (persistent to survive reverts)
persistent ghost address ghostCheckCallTarget;

// ALL_SSTORE fires on every persistent store in EVERY contract, so we must
// scope to currentContract — otherwise an SSTORE by `target` or `token`
// during exec()/transferFrom() would be a false positive.
hook ALL_SSTORE(uint slot, uint val) {
    if (executingContract == currentContract) {
        wrotePersistentStorage = true;
    }
}