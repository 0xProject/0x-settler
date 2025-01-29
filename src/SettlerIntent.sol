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

import {UnsafeMath} from "./utils/UnsafeMath.sol";

type ArrayIterator is uint256;

function __eq(ArrayIterator x, ArrayIterator y) pure returns (bool) {
    return ArrayIterator.unwrap(x) == ArrayIterator.unwrap(y);
}

function __ne(ArrayIterator x, ArrayIterator y) pure returns (bool) {
    return ArrayIterator.unwrap(x) != ArrayIterator.unwrap(y);
}

library UnsafeArray {
    function unsafeAlloc(uint256 i) internal pure returns (address[] memory r) {
        assembly ("memory-safe") {
            r := mload(0x40)
            mstore(r, i)
            mstore(0x40, add(r, add(0x20, shl(0x05, i))))
        }
    }

    function unsafeSet(address[] memory a, uint256 i, address v) internal pure {
        assembly ("memory-safe") {
            mstore(add(a, add(0x20, shl(0x05, i))), and(0xffffffffffffffffffffffffffffffffffffffff, v))
        }
    }

    function iter(address[] memory a) internal pure returns (ArrayIterator r) {
        assembly ("memory-safe") {
            r := add(0x20, a)
        }
    }

    function end(address[] memory a) internal pure returns (ArrayIterator r) {
        assembly ("memory-safe") {
            r := add(a, add(0x20, shl(0x05, mload(a))))
        }
    }

    function set(ArrayIterator i, address v) internal pure {
        assembly ("memory-safe") {
            mstore(i, and(0xffffffffffffffffffffffffffffffffffffffff, v))
        }
    }

    function next(ArrayIterator i) internal pure returns (ArrayIterator r) {
        unchecked {
            return ArrayIterator.wrap(ArrayIterator.unwrap(i) + 32);
        }
    }
}

using {__eq as ==, __ne as !=} for ArrayIterator global;

abstract contract SettlerIntent is Permit2PaymentIntent, SettlerMetaTxn {
    using UnsafeMath for uint256;
    using UnsafeArray for address[];
    using UnsafeArray for ArrayIterator;

    struct SolverList {
        uint256 length;
        mapping(address => address) next;
    }

    function _solverList() private pure returns (SolverList storage $) {
        assembly ("memory-safe") {
            $.slot := 0xe4441b0608054751d605e5c08a2210c0
        }
    }

    address private constant _SENTINEL_SOLVER = address(1);

    constructor() {
        _solverList().next[_SENTINEL_SOLVER] = _SENTINEL_SOLVER;
    }

    modifier onlyOwner() {
        (address owner, uint40 expiry) = IDeployer(DEPLOYER).authorized(Feature.wrap(uint128(_tokenId())));
        require(expiry == type(uint40).max || block.timestamp <= expiry);
        if (_operator() != owner) {
            revert IOwnable.PermissionDenied();
        }
        _;
    }

    modifier onlySolver() {
        if (_solverList().next[_operator()] == address(0)) {
            revert IOwnable.PermissionDenied();
        }
        _;
    }

    event SetSolver(address indexed solver, bool addNotRemove);

    function setSolver(address prevSolver, address solver, bool addNotRemove) external onlyOwner {
        require(solver != address(0));
        SolverList storage $ = _solverList();
        require(($.next[solver] == address(0)) == addNotRemove);
        if (addNotRemove) {
            require($.next[prevSolver] == _SENTINEL_SOLVER);
            $.next[prevSolver] = solver;
            $.next[solver] = _SENTINEL_SOLVER;
            $.length = $.length.unsafeInc();
        } else {
            require($.next[prevSolver] == solver);
            $.next[prevSolver] = $.next[solver];
            $.next[solver] = address(0);
            $.length = $.length.unsafeDec();
        }
        emit SetSolver(solver, addNotRemove);
    }

    function solvers() external view returns (address[] memory r) {
        SolverList storage $ = _solverList();
        uint256 length = $.length;

        assembly ("memory-safe") {
            // In order to save on contract size, we're doing to do some dirty hacks to return
            // `r`. In order to guarantee memory safety, we need to allocate a extra word of memory
            // before we allocate `r`.
            mstore(0x40, add(0x20, mload(0x40)))
        }
        r = UnsafeArray.unsafeAlloc(length);
        ArrayIterator i = r.iter();
        ArrayIterator end = r.end();

        address head = _SENTINEL_SOLVER;
        while (i != end) {
            head = $.next[head];
            i.set(head);
            i = i.next();
        }

        assembly ("memory-safe") {
            // This is not technically memory safe, but since we made sure that the word before `r`
            // in memory is unallocated, we are assured that we're not clobbering anything
            // important.
            let returndata := sub(r, 0x20)
            mstore(returndata, 0x20)
            return(returndata, add(0x40, shl(0x05, mload(r))))
        }
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
