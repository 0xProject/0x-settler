// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {IDeployer} from "./IDeployer.sol";
import {Feature} from "./Feature.sol";
import {Nonce} from "./Nonce.sol";
import {Revert} from "../utils/Revert.sol";

interface ISafeMinimal {
    enum Operation {
        Call,
        DelegateCall
    }

    function execTransactionFromModuleReturnData(address to, uint256 value, bytes memory data, Operation operation)
        external
        returns (bool success, bytes memory returnData);

    function isOwner(address) external view returns (bool);
}

contract ZeroExSettlerDeployerSafeModule {
    using Revert for bool;

    ISafeMinimal public immutable safe;
    IDeployer public constant deployer = IDeployer(0x00000000000004533Fe15556B1E086BB1A72cEae);

    constructor(address _safe) {
        safe = ISafeMinimal(_safe);
    }

    modifier onlyOwner() {
        require(safe.isOwner(msg.sender));
        _;
    }

    function remove(Feature feature, Nonce nonce) external onlyOwner returns (bool) {
        (bool success, bytes memory returnData) = safe.execTransactionFromModuleReturnData(
            address(deployer),
            0,
            abi.encodeWithSignature("remove(uint128,uint32)", feature, nonce),
            ISafeMinimal.Operation.Call
        );
        success.maybeRevert(returnData);
        return abi.decode(returnData, (bool));
    }

    function remove(address instance) external onlyOwner returns (bool) {
        (bool success, bytes memory returnData) = safe.execTransactionFromModuleReturnData(
            address(deployer), 0, abi.encodeWithSignature("remove(address)", (instance)), ISafeMinimal.Operation.Call
        );
        success.maybeRevert(returnData);
        return abi.decode(returnData, (bool));
    }

    function removeAll(Feature feature) external onlyOwner returns (bool) {
        (bool success, bytes memory returnData) = safe.execTransactionFromModuleReturnData(
            address(deployer), 0, abi.encodeCall(deployer.removeAll, (feature)), ISafeMinimal.Operation.Call
        );
        success.maybeRevert(returnData);
        return abi.decode(returnData, (bool));
    }
}
