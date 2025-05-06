// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

struct AccessListElem {
    address account;
    bytes32[] slots;
}
