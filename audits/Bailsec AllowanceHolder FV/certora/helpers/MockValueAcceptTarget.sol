// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

// A target whose fallback simply ACCEPTS the call (and any forwarded ETH) without
// reverting and without re-entering

contract MockValueAcceptTarget {
    fallback() external payable {}

    receive() external payable {}
}
