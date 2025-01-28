// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SettlerAbstract} from "./SettlerAbstract.sol";
import {SettlerBase} from "./SettlerBase.sol";
import {SettlerMetaTxn} from "./SettlerMetaTxn.sol";

import {Permit2PaymentAbstract} from "./core/Permit2PaymentAbstract.sol";
import {Permit2PaymentIntent, Permit2PaymentMetaTxn, Permit2Payment} from "./core/Permit2Payment.sol";

import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";

import {DEPLOYER} from "./deployer/DeployerAddress.sol";
import {IDeployer} from "./deployer/IDeployer.sol";
import {Feature} from "./deployer/Feature.sol";
import {IOwnable} from "./deployer/IOwnable.sol";

abstract contract SettlerIntent is Permit2PaymentIntent, SettlerMetaTxn {
    // @custom:storage-location erc7201:SettlerIntentSolverList
    struct SolverList {
        address[] solvers;
        mapping(address => uint256) isSolver;
    }

    function _solverList() private pure returns (SolverList storage $) {
        assembly ("memory-safe") {
            $.slot := 0x4f22d24fda4d2578949e03d6a8fd72b8e4441b0608054751d605e5c08a221000
        }
    }

    constructor() {
        SolverList storage $ = _solverList();
        uint256 $int;
        assembly ("memory-safe") {
            $int := $.slot
        }
        assert($int == (uint256(keccak256("SettlerIntentSolverList")) - 1) & ~uint256(0xff));
        _solverList().solvers.push(address(0));
        emit SetSolver(address(0), true);
    }

    modifier onlyOwner() {
        (address owner, uint40 expiry) = IDeployer(DEPLOYER).authorized(Feature.wrap(uint128(_tokenId())));
        if (_operator() != owner) {
            revert IOwnable.PermissionDenied();
        }
        if (expiry != type(uint40).max && block.timestamp > expiry) {
            revert IOwnable.PermissionDenied();
        }
        _;
    }

    modifier onlySolver() {
        if (_operator() != address(0) && _solverList().isSolver[_operator()] == 0) {
            revert IOwnable.PermissionDenied();
        }
        _;
    }

    event SetSolver(address indexed solver, bool isSolver);

    function setSolver(address solver, bool isSolver) external onlyOwner {
        require(solver != address(0));
        SolverList storage $ = _solverList();
        require(($.isSolver[solver] == 0) == isSolver);
        if (isSolver) {
            $.isSolver[solver] = $.solvers.length;
            $.solvers.push(solver);
        } else {
            uint256 oldIndex = $.isSolver[solver];
            address lastSolver = $.solvers[$.solvers.length - 1];
            $.solvers[oldIndex] = lastSolver;
            $.isSolver[lastSolver] = oldIndex;
            $.isSolver[solver] = 0;
            $.solvers.pop();
        }
        emit SetSolver(solver, isSolver);
    }

    function solvers() external view returns (address[] memory) {
        return _solverList().solvers;
    }

    function _tokenId() internal pure virtual override(SettlerAbstract, SettlerMetaTxn) returns (uint256) {
        return 4;
    }

    function _msgSender()
        internal
        view
        virtual
        // Solidity inheritance is so stupid
        override(Permit2PaymentMetaTxn, SettlerMetaTxn)
        returns (address)
    {
        return super._msgSender();
    }

    function _witnessTypeSuffix()
        internal
        pure
        virtual
        // Solidity inheritance is so stupid
        override(Permit2PaymentMetaTxn, Permit2PaymentIntent)
        returns (string memory)
    {
        return super._witnessTypeSuffix();
    }

    function _mandatorySlippageCheck() internal pure virtual override returns (bool) {
        return true;
    }

    function _hashSlippage(AllowedSlippage calldata slippage) internal pure returns (bytes32 result) {
        // This function does not check for or clean any dirty bits that might
        // exist in `slippage`. We assume that `slippage` will be used elsewhere
        // in this context and that if there are dirty bits it will result in a
        // revert later.
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            mstore(ptr, SLIPPAGE_TYPEHASH)
            calldatacopy(add(ptr, 0x20), slippage, 0x60)
            result := keccak256(ptr, 0x80)
        }
    }

    function executeMetaTxn(
        AllowedSlippage calldata slippage,
        bytes[] calldata actions,
        bytes32, /* zid & affiliate */
        address msgSender,
        bytes calldata sig
    ) public virtual override onlySolver metaTx(msgSender, _hashSlippage(slippage)) returns (bool) {
        return _executeMetaTxn(slippage, actions, sig);
    }

    function _permitToSellAmount(ISignatureTransfer.PermitTransferFrom memory permit)
        internal
        pure
        virtual
        override(Permit2PaymentAbstract, Permit2PaymentMetaTxn)
        returns (uint256 sellAmount)
    {
        sellAmount = permit.permitted.amount;
    }
}
