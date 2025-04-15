// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISettlerTakerSubmitted} from "./interfaces/ISettlerTakerSubmitted.sol";

import {MultiCallContext} from "./multicall/MultiCallContext.sol";
import {Context} from "./Context.sol";
import {TwoStepOwnable} from "./deployer/TwoStepOwnable.sol";
import {IAllowanceHolder} from "./allowanceholder/IAllowanceHolder.sol";
import {DEPLOYER as DEPLOYER_ADDRESS} from "./deployer/DeployerAddress.sol";
import {IDeployer} from "./deployer/IDeployer.sol";

import {SafeTransferLib} from "./vendor/SafeTransferLib.sol";
import {FastLogic} from "./utils/FastLogic.sol";
import {UnsafeMath} from "./utils/UnsafeMath.sol";
import {Panic} from "./utils/Panic.sol";

type Address is uint256;

/**
 * @notice Returns the address representation of a uint256.
 * @param a The uint256 value to convert to an address.
 * @return The address representation of the provided uint256 value.
 */
function get(Address a) pure returns (address) {
    return address(uint160(Address.unwrap(a) & 0x00ffffffffffffffffffffffffffffffffffffffff));
}

using {get} for Address global;

type MakerTraits is uint256;

/**
 * @notice Checks if the maker needs to unwraps WETH.
 * @param makerTraits The traits of the maker.
 * @return result A boolean indicating whether the maker needs to unwrap WETH.
 */
function unwrapWeth(MakerTraits makerTraits) pure returns (bool) {
    return MakerTraits.unwrap(makerTraits) & 0x80000000000000000000000000000000000000000000000000000000000000 != 0;
}

using {unwrapWeth} for MakerTraits global;

struct Order {
    uint256 salt;
    Address maker;
    Address receiver;
    Address makerAsset;
    Address takerAsset;
    uint256 makingAmount;
    uint256 takingAmount;
    MakerTraits makerTraits;
}

interface IPostInteraction {
    /**
     * @notice Callback method that gets called after all fund transfers
     * @param order Order being processed
     * @param extension Order extension data
     * @param orderHash Hash of the order being processed
     * @param taker Taker address
     * @param makingAmount Actual making amount
     * @param takingAmount Actual taking amount
     * @param remainingMakingAmount Order remaining making amount
     * @param extraData Extra data
     */
    function postInteraction(
        Order calldata order,
        bytes calldata extension,
        bytes32 orderHash,
        address taker,
        uint256 makingAmount,
        uint256 takingAmount,
        uint256 remainingMakingAmount,
        bytes calldata extraData
    ) external;
}

type TokenArrayIterator is uint256;

function _tokenIterator_eq(TokenArrayIterator a, TokenArrayIterator b) pure returns (bool) {
    return TokenArrayIterator.unwrap(a) == TokenArrayIterator.unwrap(b);
}

function _tokenIterator_ne(TokenArrayIterator a, TokenArrayIterator b) pure returns (bool) {
    return TokenArrayIterator.unwrap(a) != TokenArrayIterator.unwrap(b);
}

using {_tokenIterator_eq as ==, _tokenIterator_ne as !=} for TokenArrayIterator global;

library LibTokenArrayIterator {
    function iter(IERC20[] calldata a) internal pure returns (TokenArrayIterator r) {
        assembly ("memory-safe") {
            r := a.offset
        }
    }

    function end(IERC20[] calldata a) internal pure returns (TokenArrayIterator r) {
        unchecked {
            return TokenArrayIterator.wrap((a.length << 5) + TokenArrayIterator.unwrap(iter(a)));
        }
    }

    function next(TokenArrayIterator i) internal pure returns (TokenArrayIterator) {
        unchecked {
            return TokenArrayIterator.wrap(32 + TokenArrayIterator.unwrap(i));
        }
    }

    function get(IERC20[] calldata, TokenArrayIterator i) internal pure returns (IERC20 r) {
        assembly ("memory-safe") {
            r := calldataload(i)
            if shr(0xa0, r) { revert(0x00, 0x00) }
        }
    }
}

using LibTokenArrayIterator for TokenArrayIterator global;

struct Swap {
    address payable recipient;
    IERC20 sellToken;
    IERC20 buyToken;
    uint256 minBuyAmount;
    /// While Settler takes `actions` as `bytes[]`, we take it as just `bytes`; that is `abi.encode(originalActions)`.
    bytes actions;
    bytes32 zid;
}

function getActions(Swap calldata swap) pure returns (bytes calldata r) {
    assembly ("memory-safe") {
        r.offset := add(swap, calldataload(add(0x80, swap)))
        r.length := calldataload(r.offset)
        r.offset := add(0x20, r.offset)
    }
}

using {getActions} for Swap;

type SwapArrayIterator is uint256;

function _swapIterator_eq(SwapArrayIterator a, SwapArrayIterator b) pure returns (bool) {
    return SwapArrayIterator.unwrap(a) == SwapArrayIterator.unwrap(b);
}

function _swapIterator_ne(SwapArrayIterator a, SwapArrayIterator b) pure returns (bool) {
    return SwapArrayIterator.unwrap(a) != SwapArrayIterator.unwrap(b);
}

using {_swapIterator_eq as ==, _swapIterator_ne as !=} for SwapArrayIterator global;

library LibSwapArrayIterator {
    function iter(Swap[] calldata swaps) internal pure returns (SwapArrayIterator r) {
        assembly ("memory-safe") {
            r := swaps.offset
        }
    }

    function end(Swap[] calldata swaps) internal pure returns (SwapArrayIterator r) {
        unchecked {
            return SwapArrayIterator.wrap((swaps.length << 5) + SwapArrayIterator.unwrap(iter(swaps)));
        }
    }

    function next(SwapArrayIterator i) internal pure returns (SwapArrayIterator) {
        unchecked {
            return SwapArrayIterator.wrap(32 + SwapArrayIterator.unwrap(i));
        }
    }

    function get(Swap[] calldata swaps, SwapArrayIterator i) internal pure returns (Swap calldata r) {
        assembly ("memory-safe") {
            r := add(swaps.offset, calldataload(i))
        }
    }
}

using LibSwapArrayIterator for SwapArrayIterator global;

library FastDeployer {
    function fastOwnerOf(IDeployer deployer, uint256 tokenId) internal view returns (address r) {
        assembly ("memory-safe") {
            mstore(0x00, 0x6352211e) // selector for `ownerOf(uint256)`
            mstore(0x20, tokenId)

            if iszero(staticcall(gas(), deployer, 0x1c, 0x24, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if or(gt(0x20, returndatasize()), shr(0xa0, r)) { revert(0x00, 0x00) }
        }
    }

    function fastPrev(IDeployer deployer, uint128 tokenId) internal view returns (address r) {
        assembly ("memory-safe") {
            mstore(0x10, tokenId)
            mstore(0x00, 0xe2603dc200000000000000000000000000000000) // selector for `prev(uint128)` with `tokenId`'s padding

            if iszero(staticcall(gas(), deployer, 0x0c, 0x24, 0x00, 0x20)) {
                let ptr := mload(0x40)
                returndatacopy(ptr, 0x00, returndatasize())
                revert(ptr, returndatasize())
            }
            if or(gt(0x20, returndatasize()), shr(0xa0, r)) { revert(0x00, 0x00) }
        }
    }
}

contract LimitOrderFeeCollector is MultiCallContext, TwoStepOwnable, IPostInteraction {
    using SafeTransferLib for IERC20;
    using SafeTransferLib for address payable;
    using LibTokenArrayIterator for IERC20[];
    using LibSwapArrayIterator for Swap[];
    using UnsafeMath for uint256;
    using FastLogic for bool;
    using FastDeployer for IDeployer;

    address public feeCollector;
    IERC20 public immutable weth;

    modifier onlyFeeCollector() {
        if (_msgSender() != feeCollector) {
            revert PermissionDenied();
        }
        _;
    }

    address internal constant _ALLOWANCE_HOLDER_ADDRESS = 0x0000000000001fF3684f28c67538d4D072C22734;
    address internal constant _LIMIT_ORDER_PROTOCOL = 0x111111125421cA6dc452d289314280a0f8842A65;
    uint256 internal constant _BASIS = 10_000;
    uint128 internal constant _SETTLER_TOKENID = 2;
    IDeployer internal constant _DEPLOYER = IDeployer(DEPLOYER_ADDRESS);

    modifier onlyLimitOrderProtocol() {
        if (Context._msgSender() != _LIMIT_ORDER_PROTOCOL) {
            revert PermissionDenied();
        }
        _;
    }

    event SetFeeCollector(address indexed newFeeCollector);
    event GitCommit(bytes20 indexed commitHash);

    error ZeroTakingAmount(IERC20 token);
    error CounterfeitSettler(ISettlerTakerSubmitted counterfeitSettler);
    error ApproveFailed(IERC20 token);

    constructor(bytes20 gitCommit, address initialOwner, address initialFeeCollector, IERC20 weth_) {
        emit GitCommit(gitCommit);
        require(initialOwner != address(0));
        _setPendingOwner(initialOwner);
        require(initialFeeCollector != address(0));
        feeCollector = initialFeeCollector;
        emit SetFeeCollector(feeCollector);
        weth = weth_;
    }

    function setFeeCollector(address newFeeCollector) external onlyOwner returns (bool) {
        feeCollector = newFeeCollector;
        emit SetFeeCollector(newFeeCollector);
        return true;
    }

    function collectTokens(IERC20[] calldata tokens, address recipient) external onlyFeeCollector returns (bool) {
        for ((TokenArrayIterator i, TokenArrayIterator end) = (tokens.iter(), tokens.end()); i != end; i = i.next()) {
            IERC20 token = tokens.get(i);
            token.safeTransfer(recipient, token.fastBalanceOf(address(this)));
        }
        return true;
    }

    function collectEth(address payable recipient) external onlyFeeCollector returns (bool) {
        recipient.safeTransferETH(address(this).balance);
        return true;
    }

    function _requireValidSettler(ISettlerTakerSubmitted settler) private view {
        // Any revert in `ownerOf` or `prev` will be bubbled. Any error in ABIDecoding the result
        // will result in a revert without a reason string.
        if (
            _DEPLOYER.fastOwnerOf(_SETTLER_TOKENID) != address(settler)
                && _DEPLOYER.fastPrev(_SETTLER_TOKENID) != address(settler)
        ) {
            assembly ("memory-safe") {
                mstore(0x14, settler)
                mstore(0x00, 0x7a1cd8fa000000000000000000000000) // selector for `CounterfeitSettler(address)` with `settler`'s padding
                revert(0x10, 0x24)
            }
        }
    }

    modifier validSettler(ISettlerTakerSubmitted settler) {
        _requireValidSettler(settler);
        _;
    }

    function _swap(
        ISettlerTakerSubmitted settler,
        address payable recipient,
        IERC20 sellToken,
        IERC20 buyToken,
        uint256 minBuyAmount,
        bytes calldata actions,
        bytes32 zid
    ) internal returns (bool r) {
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            // encode the arguments to Settler
            calldatacopy(add(0x198, ptr), actions.offset, actions.length)
            mstore(add(0x178, ptr), actions.length)
            mstore(add(0x158, ptr), zid)
            mstore(add(0x138, ptr), 0xa0)
            mstore(add(0x118, ptr), minBuyAmount)
            mstore(add(0x1f8, ptr), buyToken)
            mstore(add(0xe4, ptr), shl(0x60, recipient)) // clears `buyToken`'s padding
            mstore(add(0xc4, ptr), 0x1fff991f000000000000000000000000) // selector for `execute((address,address,uint256),bytes[],bytes32)` with `recipient`'s padding

            for {} 1 {} {
                function bubbleRevert(p) {
                    returndatacopy(p, 0x00, returndatasize())
                    revert(p, returndatasize())
                }

                if eq(shl(0x60, sellToken), 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee000000000000000000000000) {
                    if iszero(
                        call(gas(), settler, selfbalance(), add(0xd4, ptr), add(0xc4, actions.length), 0x00, 0x20)
                    ) { bubbleRevert(ptr) }
                    if gt(0x20, returndatasize()) { revert(0x00, 0x00) }
                    r := mload(0x00)
                    break
                }

                function approveAllowanceHolder(p, token, amount) {
                    mstore(0x00, 0x095ea7b3) // selector for `approve(address,uint256)`
                    mstore(0x20, _ALLOWANCE_HOLDER_ADDRESS)
                    mstore(0x40, amount)

                    if iszero(call(gas(), token, 0x00, 0x1c, 0x44, 0x00, 0x20)) {
                        bubbleRevert(p)
                    }
                    if iszero(or(and(eq(mload(0x00), 0x01), lt(0x1f, returndatasize())), iszero(returndatasize()))) {
                        mstore(0x14, token)
                        mstore(0x00, 0xc90bb86a000000000000000000000000) // selector for `ApproveFailed(address)` with `token`'s padding
                        revert(0x10, 0x24)
                    }
                }

                approveAllowanceHolder(ptr, sellToken, 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)

                // length of the arguments to Settler
                mstore(add(0xb4, ptr), add(0xc4, actions.length))

                // encode the arguments to AllowanceHolder
                mstore(add(0x94, ptr), 0xa0)
                mstore(add(0x74, ptr), and(0xffffffffffffffffffffffffffffffffffffffff, settler))
                mstore(add(0x54, ptr), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff) // `sellAmount`
                mstore(add(0x34, ptr), sellToken)
                mstore(add(0x20, ptr), shl(0x60, settler)) // clears `sellToken`'s padding
                mstore(ptr, 0x2213bc0b000000000000000000000000) // selector for `exec(address,address,uint256,address,bytes)` with `settler`'s padding

                if iszero(call(gas(), _ALLOWANCE_HOLDER_ADDRESS, 0x00, ptr, add(0x188, actions.length), 0x00, 0x60)) {
                    bubbleRevert(ptr)
                }
                if gt(0x60, returndatasize()) { revert(0x00, 0x00) }
                r := mload(0x40)

                // collect the gas refund for zeroing the allowance slot
                approveAllowanceHolder(ptr, sellToken, 0x00)

                mstore(0x40, ptr)
                break
            }

            if shr(0x01, r) { revert(0x00, 0x00) }
        }
    }

    /// While Settler takes `actions` as `bytes[]`, we take it as just `bytes`; that is `abi.encode(originalActions)`.
    function swap(
        ISettlerTakerSubmitted settler,
        address payable recipient,
        IERC20 sellToken,
        IERC20 buyToken,
        uint256 minBuyAmount,
        bytes calldata actions,
        bytes32 zid
    ) external onlyFeeCollector validSettler(settler) returns (bool) {
        return _swap(settler, recipient, sellToken, buyToken, minBuyAmount, actions, zid);
    }

    /// While Settler takes `actions` as `bytes[]`, we take it as just `bytes`; that is `abi.encode(originalActions)`.
    function multiSwap(ISettlerTakerSubmitted settler, Swap[] calldata swaps)
        external
        onlyFeeCollector
        validSettler(settler)
        returns (bool)
    {
        for ((SwapArrayIterator i, SwapArrayIterator end) = (swaps.iter(), swaps.end()); i != end; i = i.next()) {
            Swap calldata swap_ = swaps.get(i);
            if (
                !_swap(
                    settler,
                    swap_.recipient,
                    swap_.sellToken,
                    swap_.buyToken,
                    swap_.minBuyAmount,
                    swap_.getActions(),
                    swap_.zid
                )
            ) {
                Panic.panic(Panic.GENERIC);
            }
        }
        return true;
    }

    /// @inheritdoc IPostInteraction
    function postInteraction(
        Order calldata order,
        bytes calldata /* extension */,
        bytes32 /* orderHash */,
        address /* taker */,
        uint256 /* makingAmount */,
        uint256 takingAmount,
        uint256 /* remainingMakingAmount */,
        bytes calldata extraData
    ) external override onlyLimitOrderProtocol {
        uint16 feeBps;
        assembly ("memory-safe") {
            feeBps := shr(0xf0, calldataload(extraData.offset))
        }
        if (feeBps >= _BASIS) {
            Panic.panic(Panic.ARITHMETIC_OVERFLOW);
        }
        unchecked {
            takingAmount -= (takingAmount * feeBps) / _BASIS;
        }

        address takerAsset = order.takerAsset.get();

        if (takingAmount == 0) {
            assembly ("memory-safe") {
                mstore(0x14, takerAsset)
                mstore(0x00, 0x2ca7582e000000000000000000000000) // selector for `ZeroTakingAmount(address)` with `takerAsset`'s padding
                revert(0x10, 0x24)
            }
        }

        address receiver = order.maker.get();
        if ((takerAsset == address(weth)).and(order.makerTraits.unwrapWeth())) {
            payable(receiver).safeTransferETH(takingAmount);
        } else {
            IERC20(takerAsset).safeTransfer(receiver, takingAmount);
        }
    }
}
