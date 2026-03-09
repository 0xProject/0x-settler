// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

interface IMsgSender {
    function msgSender() external view returns (address);
}
