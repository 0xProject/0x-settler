// SPDX-License-Identifier: MIT
pragma solidity ^0.8.24;

import {IDeployer} from "./IDeployer.sol";
import {Feature} from "./Feature.sol";
import {Nonce} from "./Nonce.sol";

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
    ISafeMinimal public immutable safe;
    IDeployer public constant deployer = IDeployer(0x00000000000004533Fe15556B1E086BB1A72cEae);

    bytes4 internal constant removeByNonceSelector = bytes4(keccak256("remove(uint128,uint32)"));
    bytes4 internal constant removeByInstanceSelector = bytes4(keccak256("remove(address)"));
    bytes4 internal constant removeAllSelector = IDeployer.removeAll.selector;

    constructor(address _safe) {
        safe = ISafeMinimal(_safe);
    }

    function exec(bytes calldata data) external returns (bool success, bytes memory returnData) {
        require(safe.isOwner(msg.sender));
        bytes4 selector = bytes4(data);
        require(
            selector == removeByNonceSelector || selector == removeByInstanceSelector || selector == removeAllSelector
        );
        (success, returnData) =
            safe.execTransactionFromModuleReturnData(address(deployer), 0, data, ISafeMinimal.Operation.Call);
    }
}
