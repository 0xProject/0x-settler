// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

interface IAttestation {
    function attestation() external view returns (address taker, bytes12 zid, string memory appid, address authority);
}
