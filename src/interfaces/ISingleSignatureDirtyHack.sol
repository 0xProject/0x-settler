// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {IERC5267} from "./IERC5267.sol";

import {PackedSignature} from "./PackedSignature.sol";
import {AccessListElem} from "./AccessListElem.sol";

interface ISingleSignatureDirtyHack is IERC5267 {
    error InvalidSigner(address expected, address actual);
    error NonceReplay(uint256 oldNonce, uint256 newNonce);
    error InvalidAllowance(uint256 expected, uint256 actual);
    error SignatureExpired(uint256 deadline);

    struct TransferParams {
        bytes32 structHash;
        IERC20 token;
        address from;
        address to;
        uint256 amount;
        uint256 nonce;
        uint256 deadline;
        uint256 requestedAmount;
    }

    function nonces(address) external view returns (uint256);
    function name() external view returns (string memory);
    function DOMAIN_SEPARATOR() external view returns (bytes32);

    function transferFrom(
        string calldata typeSuffix,
        TransferParams calldata transferParams,
        uint256 gasPrice,
        uint256 gasLimit,
        PackedSignature calldata sig
    ) external returns (bool);
    function transferFrom(
        string calldata typeSuffix,
        TransferParams calldata transferParams,
        uint256 gasPrice,
        uint256 gasLimit,
        AccessListElem[] calldata accessList,
        PackedSignature calldata sig
    ) external returns (bool);
    function transferFrom(
        string calldata typeSuffix,
        TransferParams calldata transferParams,
        uint256 gasPriorityPrice,
        uint256 gasPrice,
        uint256 gasLimit,
        AccessListElem[] calldata accessList,
        PackedSignature calldata sig
    ) external returns (bool);
}
