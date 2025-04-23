// SPDX-License-Identifier: MIT
pragma solidity ^0.8.25;

import {IERC20} from "@forge-std/interfaces/IERC20.sol";
import {ISettlerBase} from "./interfaces/ISettlerBase.sol";
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
import {AddressDerivation} from "./utils/AddressDerivation.sol";

type Address is uint256;

/**
 * @notice Returns the address representation of a uint256.
 * @param a The uint256 value to convert to an address.
 * @return The address representation of the provided uint256 value.
 */
function get(Address a) pure returns (address) {
    return address(uint160(0x00ffffffffffffffffffffffffffffffffffffffff & Address.unwrap(a)));
}

using {get} for Address global;

type MakerTraits is uint256;

/**
 * @notice Checks if the maker needs to unwraps WETH.
 * @param makerTraits The traits of the maker.
 * @return result A boolean indicating whether the maker needs to unwrap WETH.
 */
function unwrapWeth(MakerTraits makerTraits) pure returns (bool) {
    return (MakerTraits.unwrap(makerTraits) >> 247) & 1 != 0;
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

address constant LIMIT_ORDER_PROTOCOL = 0x111111125421cA6dc452d289314280a0f8842A65;

interface ISafeSetup {
    function setup(
        address[] calldata owners,
        uint256 threshold,
        address to,
        bytes calldata data,
        address fallbackHandler,
        address paymentToken,
        uint256 payment,
        address payable paymentReceiver
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
    IERC20 sellToken;
    uint256 minAmountOut;
    /// While Settler takes `actions` as `bytes[]`, we take it as just `bytes`; that is `abi.encode(originalActions)[32:]`.
    bytes actions;
    bytes32 zid;
}

function getActions(Swap calldata swap) pure returns (bytes calldata r) {
    assembly ("memory-safe") {
        r.offset := add(swap, calldataload(add(0x40, swap)))
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
            r := mload(0x00)
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
            r := mload(0x00)
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
    IERC20 public immutable wnative;

    address internal constant _ALLOWANCE_HOLDER_ADDRESS = 0x0000000000001fF3684f28c67538d4D072C22734;
    bytes32 private constant _ALLOWANCE_HOLDER_CODEHASH =
        0x99f5e8edaceacfdd183eb5f1da8a7757b322495b80cf7928db289a1b1a09f799;
    uint256 internal constant _BASIS = 10_000;
    uint128 internal constant _SETTLER_TOKENID = 2;
    IDeployer internal constant _DEPLOYER = IDeployer(DEPLOYER_ADDRESS);

    bytes32 private constant _SINGLETON_INITHASH = 0x49f30800a6ac5996a48b80c47ff20f19f8728812498a2a7fe75a14864fab6438;
    bytes32 private constant _FACTORY_INITHASH = 0x13d77c68fe7529013a9a57a295a785084b80e3d6ae9358c7f334752e0c8615f4;
    bytes32 private constant _FALLBACK_INITHASH = 0x272190de126b4577e187d9f00b9ca5daeae76d771965d734876891a51f9c43d8;
    bytes private constant _SAFE_CONSTRUCTOR =
        hex"608060405234801561001057600080fd5b506040516101e63803806101e68339818101604052602081101561003357600080fd5b8101908080519060200190929190505050600073ffffffffffffffffffffffffffffffffffffffff168173ffffffffffffffffffffffffffffffffffffffff1614156100ca576040517f08c379a00000000000000000000000000000000000000000000000000000000081526004018080602001828103825260228152602001806101c46022913960400191505060405180910390fd5b806000806101000a81548173ffffffffffffffffffffffffffffffffffffffff021916908373ffffffffffffffffffffffffffffffffffffffff1602179055505060ab806101196000396000f3fe608060405273ffffffffffffffffffffffffffffffffffffffff600054167fa619486e0000000000000000000000000000000000000000000000000000000060003514156050578060005260206000f35b3660008037600080366000845af43d6000803e60008114156070573d6000fd5b3d6000f3fea2646970667358221220d1429297349653a4918076d650332de1a1068c5f3e07c5c82360c277770b955264736f6c63430007060033496e76616c69642073696e676c65746f6e20616464726573732070726f7669646564";

    address private constant _TOEHOLD0 = 0x4e59b44847b379578588920cA78FbF26c0B4956C;
    address private constant _TOEHOLD1 = 0x914d7Fec6aaC8cd542e72Bca78B30650d45643d7;
    bytes32 private constant _TOEHOLD_CODEHASH = 0x2fa86add0aed31f33a762c9d88e807c475bd51d0f52bd0955754b2608f7e4989;
    address private constant _SAFE_INITIAL_OWNER = 0x6d4197897b4e776C96c04309cF1CA47179C2B543;

    event SetFeeCollector(address indexed newFeeCollector);
    event GitCommit(bytes20 indexed commitHash);

    error CounterfeitSettler(ISettlerTakerSubmitted counterfeitSettler);
    error ApproveFailed(IERC20 token);

    constructor(bytes20 gitCommit, address initialFeeCollector, IERC20 wnative_) {
        require((msg.sender == _TOEHOLD0).or(msg.sender == _TOEHOLD1));
        require(msg.sender.codehash == _TOEHOLD_CODEHASH);
        require(_ALLOWANCE_HOLDER_ADDRESS.codehash == _ALLOWANCE_HOLDER_CODEHASH);
        require(LIMIT_ORDER_PROTOCOL.code.length != 0);
        require(initialFeeCollector != address(0));
        wnative_.balanceOf(address(0)); // check that WETH is ERC20-ish

        address singleton = AddressDerivation.deriveDeterministicContract(msg.sender, bytes32(0), _SINGLETON_INITHASH);
        address factory = AddressDerivation.deriveDeterministicContract(msg.sender, bytes32(0), _FACTORY_INITHASH);
        address fallback_ = AddressDerivation.deriveDeterministicContract(msg.sender, bytes32(0), _FALLBACK_INITHASH);
        bytes32 safeInitHash = keccak256(bytes.concat(_SAFE_CONSTRUCTOR, bytes32(uint256(uint160(singleton)))));
        address[] memory safeInitialOwners = new address[](1);
        safeInitialOwners[0] = _SAFE_INITIAL_OWNER;
        bytes32 safeSalt = keccak256(
            bytes.concat(
                keccak256(
                    abi.encodeCall(
                        ISafeSetup.setup,
                        (safeInitialOwners, 1, address(0), "", fallback_, address(0), 0, payable(address(0)))
                    )
                ),
                bytes32(0)
            )
        );
        address initialOwner = AddressDerivation.deriveDeterministicContract(factory, safeSalt, safeInitHash);
        require(initialOwner.code.length != 0);

        wnative = wnative_;

        emit GitCommit(gitCommit);

        _setPendingOwner(initialOwner);

        feeCollector = initialFeeCollector;
        emit SetFeeCollector(feeCollector);
    }

    modifier onlyLimitOrderProtocol() {
        if (Context._msgSender() != LIMIT_ORDER_PROTOCOL) {
            revert PermissionDenied();
        }
        _;
    }

    function _requireFeeCollector() private view {
        if (_msgSender() != feeCollector) {
            revert PermissionDenied();
        }
    }

    modifier onlyFeeCollector() {
        _requireFeeCollector();
        _;
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

    function setFeeCollector(address newFeeCollector) external onlyOwner returns (bool) {
        require(newFeeCollector != address(0));
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

    function collectBadlyBehavedToken(IERC20 token, address recipient, uint256 amount)
        external
        onlyFeeCollector
        returns (bool)
    {
        token.safeTransfer(recipient, amount);
        return true;
    }

    function _swap(
        ISettlerTakerSubmitted settler,
        IERC20 sellToken,
        address payable recipient,
        IERC20 buyToken,
        uint256 minAmountOut,
        bytes calldata actions,
        bytes32 zid
    ) internal {
        bool success;
        assembly ("memory-safe") {
            let ptr := mload(0x40)

            // encode the arguments to Settler
            calldatacopy(add(0x178, ptr), actions.offset, actions.length)
            mstore(add(0x158, ptr), zid)
            mstore(add(0x138, ptr), 0xa0)
            mstore(add(0x118, ptr), minAmountOut)
            mstore(add(0xf8, ptr), buyToken)
            mstore(add(0xe4, ptr), shl(0x60, recipient)) // clears `buyToken`'s padding
            mstore(add(0xc4, ptr), 0x1fff991f000000000000000000000000) // selector for `execute((address,address,uint256),bytes[],bytes32)` with `recipient`'s padding

            function emptyRevert() {
                revert(0x00, 0x00)
            }

            for {} 1 {} {
                function bubbleRevert(p) {
                    returndatacopy(p, 0x00, returndatasize())
                    revert(p, returndatasize())
                }

                if eq(shl(0x60, sellToken), 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee000000000000000000000000) {
                    if iszero(
                        call(gas(), settler, selfbalance(), add(0xd4, ptr), add(0xa4, actions.length), 0x00, 0x20)
                    ) { bubbleRevert(ptr) }
                    if gt(0x20, returndatasize()) { emptyRevert() }
                    success := mload(0x00)
                    break
                }

                // Determine the sell amount exactly so that we can set an exact allowance. This is
                // done primarily to handle stupid tokens that don't allow you to set an allowance
                // greater than your balance. As a secondary concern, it lets us save gas by
                // collecting the refund for clearing the allowance slot during `transferFrom`.
                mstore(0x00, 0x70a08231) // selector for `balanceOf(address)`
                mstore(0x20, address())
                if iszero(staticcall(gas(), sellToken, 0x1c, 0x24, 0x40, 0x20)) { bubbleRevert(ptr) }
                if iszero(lt(0x1f, returndatasize())) { emptyRevert() }

                // Set the exact allowance on AllowanceHolder. The amount is already in memory 0x40.
                mstore(0x00, 0x095ea7b3) // selector for `approve(address,uint256)`
                mstore(0x20, _ALLOWANCE_HOLDER_ADDRESS)
                if iszero(call(gas(), sellToken, 0x00, 0x1c, 0x44, 0x00, 0x20)) { bubbleRevert(ptr) }
                if iszero(or(and(eq(mload(0x00), 0x01), lt(0x1f, returndatasize())), iszero(returndatasize()))) {
                    mstore(0x14, sellToken)
                    mstore(0x00, 0xc90bb86a000000000000000000000000) // selector for `ApproveFailed(address)` with `sellToken`'s padding
                    revert(0x10, 0x24)
                }

                // length of the arguments to Settler
                mstore(add(0xb4, ptr), add(0xc4, actions.length))

                // encode the arguments to AllowanceHolder
                mstore(add(0x94, ptr), 0xa0)
                mstore(add(0x74, ptr), settler)
                mcopy(add(0x54, ptr), 0x40, 0x2c) // `sellAmount` and clears `settler`'s padding
                mstore(add(0x34, ptr), sellToken)
                mstore(add(0x20, ptr), shl(0x60, settler)) // clears `sellToken`'s padding
                mstore(ptr, 0x2213bc0b000000000000000000000000) // selector for `exec(address,address,uint256,address,bytes)` with `settler`'s padding

                if iszero(
                    call(gas(), _ALLOWANCE_HOLDER_ADDRESS, 0x00, add(0x10, ptr), add(0x168, actions.length), 0x00, 0x60)
                ) { bubbleRevert(ptr) }
                if gt(0x60, returndatasize()) { emptyRevert() }
                success := mload(0x40)

                mstore(0x40, ptr)
                break
            }

            if shr(0x01, success) { emptyRevert() }
        }
        if (!success) {
            Panic.panic(Panic.GENERIC);
        }
    }

    /// While Settler takes `actions` as `bytes[]`, we take it as just `bytes`; that is `abi.encode(originalActions)[32:]`.
    function swap(
        ISettlerTakerSubmitted settler,
        IERC20 sellToken,
        ISettlerBase.AllowedSlippage calldata slippage,
        bytes calldata actions,
        bytes32 zid
    ) external onlyFeeCollector validSettler(settler) returns (bool) {
        _swap(settler, sellToken, slippage.recipient, slippage.buyToken, slippage.minAmountOut, actions, zid);
        return true;
    }

    /// While Settler takes `actions` as `bytes[]`, we take it as just `bytes`; that is `abi.encode(originalActions)[32:]`.
    function multiSwap(
        ISettlerTakerSubmitted settler,
        address payable recipient,
        IERC20 buyToken,
        Swap[] calldata swaps
    ) external onlyFeeCollector validSettler(settler) returns (bool) {
        for ((SwapArrayIterator i, SwapArrayIterator end) = (swaps.iter(), swaps.end()); i != end; i = i.next()) {
            Swap calldata swap_ = swaps.get(i);
            _swap(settler, swap_.sellToken, recipient, buyToken, swap_.minAmountOut, swap_.getActions(), swap_.zid);
        }
        return true;
    }

    function resetAllowance(IERC20 token) external onlyFeeCollector returns (bool) {
        token.safeApprove(_ALLOWANCE_HOLDER_ADDRESS, 0);
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
        address receiver = order.maker.get();
        if ((takerAsset == address(wnative)).and(order.makerTraits.unwrapWeth())) {
            payable(receiver).safeTransferETH(takingAmount);
        } else {
            IERC20(takerAsset).safeTransfer(receiver, takingAmount);
        }
    }

    receive() external payable {}
}
