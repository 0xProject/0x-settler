// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

// Re-enters AllowanceHolder TWICE during a single exec callback to exercise the
// integrated exec -> transferFrom consumption flow and the total-consumption
// bound across two consecutive callbacks.

interface IConsumptionTarget {
    function transferFromHarness(address token, address owner, address recipient, uint256 amount) external;
}

interface IMockConfig {
    function amount1() external view returns (uint256);
    function amount2() external view returns (uint256);
    function token() external view returns (address);
    function owner() external view returns (address);
    function recipient() external view returns (address);
}

contract MockDoubleCallbackTarget {

    IConsumptionTarget allowanceHolder; // linked to AllowanceHolderHarness (internal: no getter)
    IMockConfig config;                 // linked to MockCallbackConfig (internal: no getter)

    fallback() external payable {
        address t = config.token();
        address o = config.owner();
        address r = config.recipient();

        // First re-entrant consumption of the ephemeral allowance.
        allowanceHolder.transferFromHarness(t, o, r, config.amount1());
        // Second re-entrant consumption of the ephemeral allowance.
        allowanceHolder.transferFromHarness(t, o, r, config.amount2());
    }
}
