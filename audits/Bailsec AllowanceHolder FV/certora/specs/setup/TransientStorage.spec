// Summarize the transient-storage primitives via CVL functions — it avoids
// reasoning about raw EVM tload/tstore opcodes.
methods {
    function TransientStorage._get(TransientStorageBase.TSlot s) internal returns (uint256) =>
        readAllowance(s);
    function TransientStorage._set(TransientStorageBase.TSlot s, uint256 v) internal =>
        writeAllowance(s, v);
}


// transient storage slot (hash of operator, sender, token) -> allowance value
// Keyed by TSlot (the contract's user-defined value type)
persistent ghost mapping (TransientStorageBase.TSlot => uint256) allowance;


// Ghost function modeling the keccak slot derivation (operator, sender, token).
// Returns TSlot to match the contract's `_ephemeralAllowance` return type.
persistent ghost ghostEphemeralSlot(address, address, address) returns TransientStorageBase.TSlot {
    // Injectivity: different inputs → different slots
    axiom forall address op1. forall address ow1. forall address tk1.
           forall address op2. forall address ow2. forall address tk2.
        ghostEphemeralSlot(op1, ow1, tk1) == ghostEphemeralSlot(op2, ow2, tk2)
        => (op1 == op2 && ow1 == ow2 && tk1 == tk2);
}




function readAllowance(TransientStorageBase.TSlot s) returns uint256 {
    return allowance[s];
}

function writeAllowance(TransientStorageBase.TSlot s, uint256 v) {
    allowance[s] = v;
}
