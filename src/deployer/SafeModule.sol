// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {DEPLOYER} from "./DeployerAddress.sol";
import {IDeployer, IDeployerRemove} from "./IDeployer.sol";
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

contract ZeroExSettlerDeployerSafeModule is IDeployerRemove {
    using Revert for bool;

    ISafeMinimal public immutable safe;
    IDeployer public constant deployer = IDeployer(DEPLOYER);

    constructor(address _safe) {
        assert(address(this) == 0x1CeC01DC0fFEE5eB5aF47DbEc1809F2A7c601C30 || block.chainid == 31337);
        safe = ISafeMinimal(_safe);
    }

    modifier onlyOwner() {
        require(safe.isOwner(msg.sender));
        _;
    }

    function _callSafeReturnBool() internal onlyOwner returns (bool) {
        (bool success, bytes memory returnData) =
            safe.execTransactionFromModuleReturnData(address(deployer), 0, msg.data, ISafeMinimal.Operation.Call);
        success.maybeRevert(returnData);
        return abi.decode(returnData, (bool));
    }

    function remove(Feature, Nonce) external override returns (bool) {
        return _callSafeReturnBool();
    }

    function remove(address) external override returns (bool) {
        return _callSafeReturnBool();
    }

    function removeAll(Feature) external override returns (bool) {
        return _callSafeReturnBool();
    }
}
