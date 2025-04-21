// SPDX-License-Identifier: MIT
pragma solidity ^0.8.28;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";

import {AbstractContext} from "./Context.sol";
import {ALLOWANCE_HOLDER} from "./allowanceholder/AllowanceHolderContext.sol";

import {AccessListElem, TransactionEncoder} from "./utils/TransactionEncoder.sol";

abstract contract SingleSignatureDirtyHack is AbstractContext {
    error InvalidSigner(address expected, address actual);

    function verify155(
        bytes32 witness,
        uint256 nonce,
        uint256 gasPrice,
        uint256 gasLimit,
        IERC20 sellToken,
        uint256 sellAmount,
        uint256 v,
        bytes32 r,
        bytes32 s
    ) internal view {
        bytes memory data = bytes.concat(abi.encodeCall(sellToken.approve, (address(ALLOWANCE_HOLDER), sellAmount)), witness);
        address signer = TransactionEncoder.recoverSigner155(nonce, gasPrice, gasLimit, payable(address(sellToken)), 0 wei, data, v, r, s);
        if (signer != _msgSender()) {
            revert InvalidSigner(_msgSender(), signer);
        }
    }

    function verify1559(
        bytes32 witness,
        uint256 nonce,
        uint256 gasPriorityPrice,
        uint256 gasPrice,
        uint256 gasLimit,
        IERC20 sellToken,
        uint256 sellAmount,
        AccessListElem[] memory accessList,
        uint256 v,
        bytes32 r,
        bytes32 s
    ) internal view {
        bytes memory data = bytes.concat(abi.encodeCall(sellToken.approve, (address(ALLOWANCE_HOLDER), sellAmount)), witness);
        address signer = TransactionEncoder.recoverSigner1559(nonce, gasPriorityPrice, gasPrice, gasLimit, payable(address(sellToken)), 0 wei, data, accessList, v, r, s);
        if (signer != _msgSender()) {
            revert InvalidSigner(_msgSender(), signer);
        }
    }
}
