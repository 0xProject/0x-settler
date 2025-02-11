// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {SettlerAbstract} from "./SettlerAbstract.sol";
import {SettlerBase} from "./SettlerBase.sol";
import {SettlerMetaTxn} from "./SettlerMetaTxn.sol";

import {Permit2PaymentAbstract} from "./core/Permit2PaymentAbstract.sol";
import {Permit2PaymentIntent, Permit2PaymentMetaTxn, Permit2Payment} from "./core/Permit2Payment.sol";

import {AbstractContext, Context} from "./Context.sol";
import {MultiCallContext} from "./multicall/MultiCallContext.sol";

import {ISignatureTransfer} from "@permit2/interfaces/ISignatureTransfer.sol";

import {DEPLOYER} from "./deployer/DeployerAddress.sol";
import {IDeployer} from "./deployer/IDeployer.sol";
import {Feature} from "./deployer/Feature.sol";
import {IOwnable} from "./deployer/IOwnable.sol";

abstract contract SettlerIntent is Permit2PaymentIntent, SettlerMetaTxn, MultiCallContext {
    bytes32 private constant _SOLVER_LIST_BASE_SLOT = 0x00000000000000000000000000000000e4441b0608054751d605e5c08a2210bf; // uint128(uint256(keccak256("SettlerIntentSolverList")) - 1)
    bytes32 private constant _SOLVER_LIST_START_SLOT =
        0x165458a486c543a8294bbc8a8476cd9020f962f9e80991591ef8c2860c5c5490; // keccak256(abi.encode(_SENTINEL_SOLVER, _SOLVER_LIST_BASE_SLOT))

    /// This mapping forms a circular singly-linked list that traverses all the authorized callers
    /// of `executeMetaTxn`. The head and tail of the list is `address(1)`, which is the constant
    /// `_SENTINEL_SOLVER`. No view function is provided for accessing this mapping. You'll have to
    /// use an RPC to read storage directly and reconstruct the list that way. As a consequence of
    /// the structure of this list, the check for whether an address is on the list is extremely
    /// simple: `_$()[query] != address(0)`. This technique is cribbed from Safe{Wallet}
    function _$() private pure returns (mapping(address => address) storage $) {
        assembly ("memory-safe") {
            $.slot := _SOLVER_LIST_BASE_SLOT
        }
    }

    address private constant _SENTINEL_SOLVER = 0x0000000000000000000000000000000000000001;

    constructor() {
        assert(_SOLVER_LIST_BASE_SLOT == bytes32(uint256(uint128(uint256(keccak256("SettlerIntentSolverList")) - 1))));
        assert(_SOLVER_LIST_START_SLOT == keccak256(abi.encode(_SENTINEL_SOLVER, _SOLVER_LIST_BASE_SLOT)));
        _$()[_SENTINEL_SOLVER] = _SENTINEL_SOLVER;
    }

    modifier onlyOwner() {
        // Solidity generates extremely bloated code for the following block, so it has been
        // rewritten in assembly so as not to blow out the contract size limit
        /*
        (address owner, uint40 expiry) = IDeployer(DEPLOYER).authorized(Feature.wrap(uint128(_tokenId())));
        */
        address deployer_ = DEPLOYER;
        uint256 tokenId_ = _tokenId();
        address owner;
        uint40 expiry;
        assembly ("memory-safe") {
            // We lay out the calldata in memory in the first 2 slots. The first slot is the
            // selector, but aligned incorrectly (this significantly saves on contract size). The
            // second slot is the token ID. Therefore calldata starts at offset 0x1c (32 - 4) and is
            // 0x24 bytes long (32 + 4)
            mstore(0x00, 0x2bb83987) // selector for `authorized(uint128)`
            mstore(0x20, tokenId_)

            // Perform the call and bubble any revert. The expected returndata (2 arguments, each 1
            // slot) is copied back into the first 2 slots of memory.
            if iszero(staticcall(gas(), deployer_, 0x1c, 0x24, 0x00, 0x40)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }

            // If calldata is short (we need at least 64 bytes), revert with an empty reason.
            if iszero(gt(returndatasize(), 0x3f)) { revert(0x00, 0x00) }

            // Load the return values that were automatically written into the first 2 slots of
            // memory.
            owner := mload(0x00)
            expiry := mload(0x20)

            // If there are any dirty bits in the return values, revert with an empty reason.
            if or(shr(0xa0, owner), shr(0x28, expiry)) { revert(0x00, 0x00) }
        }

        // Check that the owner actually exists, that is that their authority hasn't expired.
        require(expiry == type(uint40).max || block.timestamp <= expiry);

        // Check that the caller (in this case `_operator()`, because we aren't using the special
        // transient-storage taker logic) is the owner.
        if (_operator() != owner) {
            revert IOwnable.PermissionDenied();
        }
        _;
    }

    modifier onlySolver() {
        if (_$()[_operator()] == address(0)) {
            revert IOwnable.PermissionDenied();
        }
        _;
    }

    error InvalidSolver(address prev, address solver);

    /// This pattern is cribbed from Safe{Wallet}. See `OwnerManager.sol` from
    /// 0x3E5c63644E683549055b9Be8653de26E0B4CD36E.
    function setSolver(address prev, address solver, bool addNotRemove) external onlyOwner {
        // Solidity generates extremely bloated code for the following block, so it has been
        // rewritten in assembly so as not to blow out the contract size limit
        /*
        require(solver != address(0));
        mapping(address => address) storage $ = _$();
        require(($[solver] == address(0)) == addNotRemove);
        if (addNotRemove) {
            require($[prev] == _SENTINEL_SOLVER);
            $[prev] = solver;
            $[solver] = _SENTINEL_SOLVER;
        } else {
            require($[prev] == solver);
            $[prev] = $[solver];
            $[solver] = address(0);
        }
        */
        assembly ("memory-safe") {
            // Clean dirty bits.
            prev := and(0xffffffffffffffffffffffffffffffffffffffff, prev)
            solver := and(0xffffffffffffffffffffffffffffffffffffffff, solver)

            // A solver of zero is special-cased. It is forbidden to set it because that would
            // corrupt the list.
            let fail := iszero(solver)

            // Derive the slot for `solver` and load it.
            mstore(0x00, solver)
            mstore(0x20, _SOLVER_LIST_BASE_SLOT)
            let solverSlot := keccak256(0x00, 0x40)
            let solverSlotValue := and(0xffffffffffffffffffffffffffffffffffffffff, sload(solverSlot))

            // If the slot contains zero, `addNotRemove` must be true (we are adding a new
            // solver). Likewise if the slot contains nonzero, `addNotRemove` must be false (we are
            // removing one).
            fail := or(fail, xor(iszero(solverSlotValue), addNotRemove))

            // Derive the slot for `prev`.
            mstore(0x00, prev)
            let prevSlot := keccak256(0x00, 0x40)

            // This is a very fancy way of writing:
            //     expectedPrevSlotValue = addNotRemove ? _SENTINEL_SOLVER : solver
            //     newPrevSlotValue = addNotRemove ? solver : solverSlotValue
            let expectedPrevSlotValue := xor(solver, mul(xor(_SENTINEL_SOLVER, solver), addNotRemove))
            let newPrevSlotValue := xor(solverSlotValue, mul(xor(solverSlotValue, solver), addNotRemove))

            // Check that the value for `prev` matches the value for `solver`. If we are adding a
            // new solver, then `prev` must be the last element of the list (it points at
            // `_SENTINEL_SOLVER`). If we are removing an existing solver, then `prev` must point at
            // `solver.
            fail :=
                or(fail, xor(and(0xffffffffffffffffffffffffffffffffffffffff, sload(prevSlot)), expectedPrevSlotValue))

            // Update the linked list. This either points `$[prev]` at `$[solver]` and zeroes
            // `$[solver]` or it points `$[prev]` at `solver` and points `$[solver]` at
            // `_SENTINEL_SOLVER`
            sstore(prevSlot, newPrevSlotValue)
            sstore(solverSlot, addNotRemove)

            // If any of the checks failed, revert. This check is deferred because it makes the
            // contract substantially smaller.
            if fail {
                mstore(0x00, 0xe2b339fd) // selector for `InvalidSolver(address,address)`
                mstore(0x20, prev)
                mstore(0x40, solver)
                revert(0x1c, 0x44)
            }
        }
    }

    /// This function is not intended to be called on-chain. It's only for being `eth_call`'d. There
    /// is a somewhat obvious DoS vector here if called on-chain, so just don't do that.
    function getSolvers() external view returns (address[] memory) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            let len
            {
                let start := add(0x40, ptr)
                let i := start
                for {
                    mstore(0x20, _SOLVER_LIST_BASE_SLOT)
                    let x := and(0xffffffffffffffffffffffffffffffffffffffff, sload(_SOLVER_LIST_START_SLOT))
                } xor(x, _SENTINEL_SOLVER) {
                    i := add(0x20, i)
                    x := and(0xffffffffffffffffffffffffffffffffffffffff, sload(keccak256(0x00, 0x40)))
                } {
                    mstore(i, x)
                    mstore(0x00, x)
                }
                len := sub(i, start)
            }

            mstore(ptr, 0x20)
            mstore(add(0x20, ptr), shr(0x05, len))
            return(ptr, add(0x40, len))
        }
    }

    function _tokenId() internal pure virtual override(SettlerAbstract, SettlerMetaTxn) returns (uint256) {
        return 4;
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

    function _isForwarded() internal view virtual override(AbstractContext, Context, MultiCallContext) returns (bool) {
        return Context._isForwarded(); // false
    }

    // Solidity inheritance is stupid
    function _msgData()
        internal
        view
        virtual
        override(AbstractContext, Context, MultiCallContext)
        returns (bytes calldata)
    {
        return super._msgData();
    }

    function _msgSender()
        internal
        view
        virtual
        override(Permit2PaymentMetaTxn, SettlerMetaTxn, MultiCallContext)
        returns (address)
    {
        return super._msgSender();
    }

    function _witnessTypeSuffix()
        internal
        pure
        virtual
        override(Permit2PaymentMetaTxn, Permit2PaymentIntent)
        returns (string memory)
    {
        return super._witnessTypeSuffix();
    }
}
