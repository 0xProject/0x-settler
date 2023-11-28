// SPDX-License-Identifier: MIT
pragma solidity ^0.8.21;

import {ISignatureTransfer} from "permit2/src/interfaces/ISignatureTransfer.sol";
import {IAllowanceTransfer} from "permit2/src/interfaces/IAllowanceTransfer.sol";

interface IAllowanceHolder {
    struct TransferDetails {
        address token;
        address recipient;
        uint256 amount;
    }

    function holderTransferFrom(address owner, TransferDetails[] calldata transferDetails) external returns (bool);

    function execute(
        address operator,
        ISignatureTransfer.TokenPermissions[] calldata permits,
        address payable target,
        bytes calldata data
    ) external payable returns (bytes memory result);

    function executeFirstTime(
        address operator,
        IAllowanceTransfer.PermitSingle calldata firstPermit,
        bytes memory sig,
        ISignatureTransfer.TokenPermissions[] calldata permits,
        address payable target,
        bytes calldata data
    ) external payable returns (bytes memory result);
}
