import "./base/allowanceHolder_transientStorage.spec";

// UT-25: the production assembly packing (the 60 bytes fed to keccak256) is exactly
// abi.encodePacked(operator, owner, token)
rule ephemeralPackingMatchesAbiEncodePacked(address operator, address owner, address token) {
    bytes32 pw0;
    bytes32 pw1;
    bytes32 rw0;
    bytes32 rw1;

    pw0, pw1 = prodPreimageWords(operator, owner, token);
    rw0, rw1 = refPreimageWords(operator, owner, token);

    assert pw0 == rw0,
        "preimage[0:32) (operator ++ owner[0:12]) must match abi.encodePacked";
    assert pw1 == rw1,
        "preimage[32:60) (owner[12:20] ++ token) must match abi.encodePacked";
}

// UT-26: the real _ephemeralAllowance (unsummarized, real keccak) equals an
// identical-construction transcription
rule realEphemeralEqualsTranscription(address operator, address owner, address token) {
    bytes32 real = ephemeralSlotHarness(operator, owner, token);
    bytes32 transcribed = transcribedSlotHarness(operator, owner, token);

    assert real == transcribed,
        "real _ephemeralAllowance must equal the identical-construction transcription";
}

// UT-27: round-trip — tload(s) after tstore(s, v) returns exactly v
rule transientRoundTrip(bytes32 s, uint256 v) {
    uint256 readBack = setThenGet(s, v);
    assert readBack == v, "tload(s) after tstore(s, v) must equal v";
}

// UT-28: last write wins — tstore(s, v1); tstore(s, v2); tload(s) == v2
rule transientOverwrite(bytes32 s, uint256 v1, uint256 v2) {
    uint256 readBack = setOverwriteThenGet(s, v1, v2);
    assert readBack == v2, "second tstore to the same slot must overwrite the first";
}

// UT-29: slot independence — writing a different slot s2 does not disturb s1
rule transientSlotIndependence(bytes32 s1, uint256 v1, bytes32 s2, uint256 v2) {
    require(s1 != s2, "s1 and s2 must be different");
    uint256 readBackS1 = setTwoThenGet(s1, v1, s2, v2);
    assert readBackS1 == v1, "writing slot s2 must not change slot s1";
}

// VS-03: Distinct (operator, owner, token) triples map to distinct ephemeral slots (no aliasing)
rule allowanceSlotInjectivity(env e) {
    //input variables
    address operator1;
    address owner1;
    address token1;
    address operator2;
    address owner2;
    address token2;

    //function calls
    bytes32 slotA  = TransientStorageHarness.ephemeralAllowanceHarness(e, operator1, owner1, token1);
    bytes32 slotB = TransientStorageHarness.ephemeralAllowanceHarness(e, operator2, owner2, token2);

    //assert that the allowance slots are different
    assert(operator1 != operator2 || owner1 != owner2 || token1 != token2 => slotA != slotB, 
                    "Allowance slots must be different for different inputs");
    assert(slotA == slotB => operator1 == operator2 && owner1 == owner2 && token1 == token2, 
                    "Allowance slots must be the same for the same inputs");
}

