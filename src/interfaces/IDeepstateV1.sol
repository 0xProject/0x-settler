// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

/// @notice Minimal interface for the canonical Deepstate V1 deployment on Robinhood Chain.
/// @dev The canonical engine is deployed at 0x6cf19308C22FC82ea620Fa0B3E94948d20f27B96.
interface IDeepstateV1 {
    struct FillParams {
        address token0;
        address token1;
        uint256 epoch;
        bytes32 order;
        bool isBid;
        bool noRest;
        bool fillOrKill;
    }

    function fill(FillParams calldata params) external payable returns (bytes32 restingOrder);
}
