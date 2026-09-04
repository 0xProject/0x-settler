using TransientStorageHarness as TransientStorageHarness;

methods {
    // §3 transient round-trip (real tload/tstore)
    function setThenGet(bytes32, uint256) external returns (uint256) envfree;
    function setTwoThenGet(bytes32, uint256, bytes32, uint256) external returns (uint256) envfree;
    function setOverwriteThenGet(bytes32, uint256, uint256) external returns (uint256) envfree;

    // §2/§3 ephemeral keccak formula (preimage comparison)
    function ephemeralSlotHarness(address, address, address) external returns (bytes32) envfree;
    function transcribedSlotHarness(address, address, address) external returns (bytes32) envfree;
    function prodPreimageWords(address, address, address) external returns (bytes32, bytes32) envfree;
    function refPreimageWords(address, address, address) external returns (bytes32, bytes32) envfree;
}
